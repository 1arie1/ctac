from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass

from ctac.analysis import analyze_dsa, analyze_use_before_def, extract_def_use
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    TacCmd,
)
from ctac.graph import Cfg
from ctac.ir.models import TacBlock, TacProgram
from ctac.smt.cfg import CFG_ENCODERS, CfgEmit, build_cfg_input
from ctac.smt.encoding.base import EncoderContext, SmtEncoder, SmtEncodingError
from ctac.smt.encoding.path_skeleton import (
    block_guard,
    block_id_for_reachability_var,
    blk_var_name,
    sanitize_ident,
)
from ctac.smt.vc.builder import BlockBuilder, VCBuilder
from ctac.smt.vc.config import (
    AssertionPolicy,
    FactKind,
    FactPlacement,
    VCConfig,
)
from ctac.smt.vc.script import VCScript
from ctac.smt.vc.tac import TacExprLowerer, _range_refinement_for_symbol
from ctac.smt.vc.terms import Bool, Int, Sort, Term, term, true


_SUPPORTED_CMD_TYPES = (
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    AssertCmd,
    JumpCmd,
    JumpiCmd,
    AnnotationCmd,
    LabelCmd,
)


@dataclass
class SeaEncoder(SmtEncoder):
    name: str = "sea"

    def encode(self, ctx: EncoderContext) -> VCScript:
        self._reject_unsupported_options(ctx)
        program = ctx.tac_file.program
        if not program.blocks:
            raise SmtEncodingError("program has no blocks")
        self._check_supported_commands(program)

        du = extract_def_use(program)
        dsa = analyze_dsa(program, def_use=du)
        if not dsa.is_valid:
            first = dsa.issues[0]
            raise SmtEncodingError(
                f"DSA precondition failed: {first.kind} at {first.block_id}:{first.cmd_index}"
            )
        ubd = analyze_use_before_def(program, def_use=du)
        if ubd.issues:
            first = ubd.issues[0]
            raise SmtEncodingError(
                f"use-before-def: {first.symbol!r} at "
                f"{first.block_id}:{first.cmd_index} ({first.cmd_kind})"
        )

        entry = program.blocks[0].id
        dynamic_points = {(row.block_id, row.cmd_index) for row in dsa.dynamic_assignments}
        symbol_sorts = _canonical_symbol_sorts(ctx.tac_file.symbol_sorts)
        vc = VCBuilder(
            VCConfig(
                produce_unsat_cores=ctx.unsat_core,
                globalize_eligible_facts=not ctx.guard_statics,
                annotate_with_cmds=ctx.annotate_with_cmds,
                assertion_policy=AssertionPolicy(
                    grouped_kinds=(
                        frozenset({FactKind.DEF, FactKind.ASSUME, FactKind.RANGE})
                        if ctx.guard_statics
                        else frozenset()
                    )
                ),
            )
        )
        aliases = _define_reachability_aliases(vc, program, symbol_sorts, entry)
        expr = TacExprLowerer(vc, symbol_sorts, symbol_aliases=aliases)

        self._emit_static_blocks(
            vc,
            expr,
            program,
            entry,
            dynamic_points,
        )
        self._emit_dynamic_defs(
            vc,
            expr,
            program,
            dsa.dynamic_assignments,
            symbol_sorts,
            entry,
            guard_dynamics=ctx.guard_dynamics,
        )
        self._emit_cfg(vc, program, aliases, entry, ctx.cfg_encoding)
        self._emit_assert_objective(vc, expr, ctx, entry)
        return vc.script()

    def _reject_unsupported_options(self, ctx: EncoderContext) -> None:
        unsupported: list[str] = []
        if ctx.tight_logic:
            unsupported.append("--tight-logic")
        if ctx.guard_axioms:
            unsupported.append("--guard-axioms")
        if ctx.narrow_range:
            unsupported.append("--narrow-range")
        if ctx.bv_add_sub_axiom != "no-mod":
            unsupported.append("--bv-add-sub-mod-axiom")
        if ctx.store_reduce:
            unsupported.append("--store-reduce")
        if ctx.inline_scalars:
            unsupported.append("--inline-scalars")
        if unsupported:
            raise SmtEncodingError(
                f"encoding 'sea' does not support {', '.join(unsupported)} yet"
            )

    def _check_supported_commands(self, program: TacProgram) -> None:
        for block in program.blocks:
            for idx, cmd in enumerate(block.commands):
                if isinstance(cmd, _SUPPORTED_CMD_TYPES):
                    continue
                kind = type(cmd).__name__
                head = getattr(cmd, "head", None)
                head_part = f", head={head!r}" if head else ""
                raise SmtEncodingError(
                    f"unsupported command at {block.id}:{idx} ({kind}{head_part}): "
                    f"{cmd.raw!r}"
                )

    def _emit_static_blocks(
        self,
        vc: VCBuilder,
        expr: TacExprLowerer,
        program: TacProgram,
        entry: str,
        dynamic_points: set[tuple[str, int]],
    ) -> None:
        for block in Cfg(program).ordered_blocks():
            guard = _block_guard_term(vc, block.id, entry)
            with vc.block(block.id, guard=guard) as builder:
                i = 0
                while i < len(block.commands):
                    if (block.id, i) in dynamic_points:
                        i += 1
                        continue
                    havoc_range = _havoc_range_event(block, i)
                    if havoc_range is not None:
                        cmd, lo, hi = havoc_range
                        lhs = _canon(cmd.lhs)
                        if lhs in expr.symbol_aliases:
                            i += 2
                            continue
                        x = vc.const(lhs, _sort_for(symbol_sorts=expr.symbol_sorts, name=lhs))
                        expr.require_sort(x, Int, lhs)
                        vc.range(
                            x,
                            lo=lo,
                            hi=hi,
                            scope="current",
                            name=vc.auto_name("havoc_range", x.text),
                            placement=FactPlacement.ELIGIBLE_GLOBAL,
                        )
                        i += 2
                        continue
                    cmd = block.commands[i]
                    with vc.stmt(cmd.meta_index, cmd.raw):
                        self._emit_static_command(
                            vc,
                            builder,
                            expr,
                            cmd,
                            block.id,
                        )
                    i += 1

    def _emit_static_command(
        self,
        vc: VCBuilder,
        builder: BlockBuilder,
        expr: TacExprLowerer,
        cmd: TacCmd,
        block_id: str,
    ) -> None:
        if isinstance(cmd, AssignExpCmd):
            lhs_name = _canon(cmd.lhs)
            if _is_map(expr.symbol_sorts, lhs_name):
                _emit_map_store(vc, expr, cmd)
                return
            lhs = vc.const(lhs_name, _sort_for(symbol_sorts=expr.symbol_sorts, name=lhs_name))
            rhs = expr.lower_scalar(cmd.rhs)
            expr.require_assignment_sort(lhs, rhs, cmd.rhs)
            builder.def_(
                lhs,
                rhs,
                name=vc.auto_name("def", lhs.text),
                placement=FactPlacement.ELIGIBLE_GLOBAL,
            )
        elif isinstance(cmd, AssignHavocCmd):
            lhs = _canon(cmd.lhs)
            if lhs in expr.symbol_aliases:
                return
            if _is_map(expr.symbol_sorts, lhs):
                vc.bytemap.havoc(lhs)
            else:
                lhs_term = vc.const(lhs, _sort_for(symbol_sorts=expr.symbol_sorts, name=lhs))
                if lhs_term.sort is Int:
                    vc.range(
                        lhs_term,
                        lo=0,
                        hi=_BV256_MAX,
                        scope="current",
                        name=vc.auto_name("havoc_range", lhs),
                        placement=FactPlacement.ELIGIBLE_GLOBAL,
                    )
        elif isinstance(cmd, AssumeExpCmd):
            vc.fact(
                FactKind.ASSUME,
                expr.lower_bool(cmd.condition),
                scope="current",
                name=vc.auto_name("assume"),
                origin="assume",
            )
        elif isinstance(cmd, AssertCmd):
            return
        elif isinstance(cmd, (JumpCmd, JumpiCmd, AnnotationCmd, LabelCmd)):
            return
        elif isinstance(cmd, RawCmd):
            raise SmtEncodingError(f"unsupported raw command in block {block_id}: {cmd.raw!r}")

    def _emit_dynamic_defs(
        self,
        vc: VCBuilder,
        expr: TacExprLowerer,
        program: TacProgram,
        rows: tuple,
        symbol_sorts: dict[str, str],
        entry: str,
        *,
        guard_dynamics: bool,
    ) -> None:
        by_id = program.block_by_id()
        rows_by_symbol: dict[str, list] = defaultdict(list)
        for row in rows:
            sym = _canon(row.symbol)
            if _is_map(symbol_sorts, sym):
                raise SmtEncodingError("encoding 'sea' does not support dynamic bytemaps yet")
            rows_by_symbol[sym].append(row)
        block_pos = {b.id: i for i, b in enumerate(Cfg(program).ordered_blocks())}
        for sym, sym_rows in sorted(rows_by_symbol.items()):
            cases: list[tuple[Term, Term]] = []
            for row in sorted(sym_rows, key=lambda r: block_pos.get(r.block_id, 10**9)):
                block = by_id[row.block_id]
                cmd = block.commands[row.cmd_index]
                guard = _block_guard_term(vc, row.block_id, entry)
                with vc.block(row.block_id, guard=guard), vc.stmt(row.cmd_index, row.raw):
                    if isinstance(cmd, AssignExpCmd):
                        rhs = expr.lower_scalar(cmd.rhs)
                    elif isinstance(cmd, AssignHavocCmd):
                        rhs = _fresh_havoc(
                            vc,
                            sym,
                            row.block_id,
                            row.cmd_index,
                            _sort_for(symbol_sorts=symbol_sorts, name=sym),
                        )
                        if rhs.sort is Int:
                            vc.range(
                                rhs,
                                lo=0,
                                hi=_BV256_MAX,
                                scope=None,
                                name=vc.auto_name("havoc_range", rhs.text),
                                placement=FactPlacement.GLOBAL,
                            )
                    else:
                        raise SmtEncodingError(
                            f"dynamic assignment for {sym} must be AssignExpCmd/AssignHavocCmd"
                        )
                    expr.require_assignment_sort(
                        vc.const(sym, _sort_for(symbol_sorts=symbol_sorts, name=sym)),
                        rhs,
                        cmd.rhs if isinstance(cmd, AssignExpCmd) else sym,
                    )
                cases.append((guard, rhs))
            vc.dynamic_def(
                vc.const(sym, _sort_for(symbol_sorts=symbol_sorts, name=sym)),
                tuple(cases),
                guarded=guard_dynamics,
            )

    def _emit_cfg(
        self,
        vc: VCBuilder,
        program: TacProgram,
        aliases: dict[str, Term],
        entry: str,
        cfg_encoding: str,
    ) -> None:
        symbol_terms = {
            name: alias.smt()
            for name, alias in aliases.items()
        }
        cfg_input = build_cfg_input(
            program,
            entry_block_id=entry,
            symbol_term=symbol_terms,
        )
        cfg_encoder = CFG_ENCODERS.get(cfg_encoding)
        if cfg_encoder is None:
            raise SmtEncodingError(
                f"unknown cfg_encoding {cfg_encoding!r}; available: {', '.join(sorted(CFG_ENCODERS))}"
            )
        cfg_emit = CfgEmit(
            add_constraint=lambda raw: vc.raw_fact(raw, origin="cfg"),
            add_decl=lambda name, sort: vc.const(name, Bool if sort == "Bool" else Int),
        )
        cfg_encoder(cfg_input, cfg_emit)

    def _emit_assert_objective(
        self,
        vc: VCBuilder,
        expr: TacExprLowerer,
        ctx: EncoderContext,
        entry: str,
    ) -> None:
        assert_block_guard = _block_guard_term(vc, ctx.assert_site.block_id, entry)
        with vc.block(ctx.assert_site.block_id, guard=assert_block_guard):
            pred = expr.lower_bool(ctx.assert_site.command.predicate)
        vc.assert_failure_objective(vc.const("BLK_EXIT", Bool), assert_block_guard, pred)


def _define_reachability_aliases(
    vc: VCBuilder,
    program: TacProgram,
    symbol_sorts: dict[str, str],
    entry: str,
) -> dict[str, Term]:
    aliases: dict[str, Term] = {}
    block_ids = {block.id for block in program.blocks}
    for name in sorted(symbol_sorts):
        name = _canon(name)
        block_id = block_id_for_reachability_var(name)
        if block_id not in block_ids:
            continue
        guard = _block_guard_term(vc, block_id, entry)
        vc.define_fun(name, (), Bool, guard)
        aliases[name] = term(name, Bool)
    return aliases


def _block_guard_term(vc: VCBuilder, block_id: str, entry: str) -> Term:
    guard = block_guard(block_id, entry_block_id=entry)
    if guard == "true":
        return true()
    return vc.const(blk_var_name(block_id), Bool)


def _emit_map_store(vc: VCBuilder, expr: TacExprLowerer, cmd: AssignExpCmd) -> None:
    if not isinstance(cmd.rhs, ApplyExpr) or cmd.rhs.op != "Store" or len(cmd.rhs.args) != 3:
        raise SmtEncodingError(f"bytemap assignment {cmd.lhs!r} requires Store RHS")
    base = expr.lower_map(cmd.rhs.args[0])
    index = expr.lower_int(cmd.rhs.args[1])
    value = expr.lower_int(cmd.rhs.args[2])
    vc.bytemap.store(_canon(cmd.lhs), base, index, value)


def _havoc_range_event(block: TacBlock, index: int) -> tuple[AssignHavocCmd, int, int] | None:
    if index + 1 >= len(block.commands):
        return None
    cmd = block.commands[index]
    assume = block.commands[index + 1]
    if not isinstance(cmd, AssignHavocCmd) or not isinstance(assume, AssumeExpCmd):
        return None
    lo, hi = _range_refinement_for_symbol(assume.condition, _canon(cmd.lhs))
    if lo is None and hi is None:
        return None
    lo = max(0, lo) if lo is not None else 0
    hi = min(_BV256_MAX, hi) if hi is not None else _BV256_MAX
    if lo > hi:
        raise SmtEncodingError(f"invalid havoc range for {cmd.lhs}: {lo} > {hi}")
    return cmd, lo, hi


def _fresh_havoc(
    vc: VCBuilder,
    sym: str,
    block_id: str,
    cmd_index: int,
    sort: Sort,
) -> Term:
    name = f"HAVOC_{sanitize_ident(sym)}_{sanitize_ident(block_id)}_{cmd_index}"
    return vc.const(name, sort)


def _is_map(symbol_sorts: dict[str, str], name: str) -> bool:
    return symbol_sorts.get(_canon(name)) in {"bytemap", "ghostmap"}


def _sort_for(*, symbol_sorts: dict[str, str], name: str) -> Sort:
    return Bool if symbol_sorts.get(_canon(name)) == "bool" else Int


def _canon(symbol: str) -> str:
    return canonical_symbol(symbol, strip_var_suffixes=True)


def _canonical_symbol_sorts(symbol_sorts: dict[str, str]) -> dict[str, str]:
    return {_canon(name): sort for name, sort in symbol_sorts.items()}


_BV256_MAX = (1 << 256) - 1
