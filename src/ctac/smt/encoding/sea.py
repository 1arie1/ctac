from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass

from ctac.analysis import analyze_dsa, analyze_use_before_def, extract_def_use
from ctac.analysis.model import DefUseResult, DefinitionSite, DsaDynamicAssignment, DsaResult
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
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
from ctac.smt.vc.tac import TacExprLowerer, _lower_map_body, _range_refinement_for_symbol
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

_INLINE_LINEAR_OPS = frozenset({"Add", "Sub", "IntAdd", "IntSub"})
_INLINE_LINEAR_SCALE_OPS = frozenset({"Mul", "IntMul"})


@dataclass
class SeaEncoder(SmtEncoder):
    name: str = "sea"

    def encode(self, ctx: EncoderContext) -> VCScript:
        self._reject_unsupported_options(ctx)
        state = prepare_sea_state(ctx)
        emit_static_blocks(state)
        dynamic_defs = collect_dynamic_defs(state)
        if dynamic_defs:
            state.vc.section("dynamic assignments")
        emit_dynamic_defs(state, dynamic_defs, guarded=ctx.guard_dynamics)
        emit_cfg(state, ctx.cfg_encoding)
        emit_assert_objective(state, ctx)
        return state.vc.script()

    def _reject_unsupported_options(self, ctx: EncoderContext) -> None:
        unsupported: list[str] = []
        if ctx.tight_logic:
            unsupported.append("--tight-logic")
        if ctx.narrow_range:
            unsupported.append("--narrow-range")
        if ctx.bv_add_sub_axiom != "no-mod":
            unsupported.append("--bv-add-sub-mod-axiom")
        if ctx.store_reduce:
            unsupported.append("--store-reduce")
        if unsupported:
            raise SmtEncodingError(f"encoding 'sea' does not support {', '.join(unsupported)} yet")


@dataclass(frozen=True)
class SeaEncodingState:
    ctx: EncoderContext
    program: TacProgram
    du: DefUseResult
    dsa: DsaResult
    vc: VCBuilder
    expr: TacExprLowerer
    entry: str
    symbol_sorts: dict[str, str]
    aliases: dict[str, Term]
    dynamic_points: frozenset[tuple[str, int]]
    inline_points: frozenset[tuple[str, int]]


@dataclass(frozen=True)
class DynamicDefCase:
    symbol: str
    block_id: str
    cmd_index: int
    guard: Term
    rhs: Term


def prepare_sea_state(ctx: EncoderContext) -> SeaEncodingState:
    program = ctx.tac_file.program
    if not program.blocks:
        raise SmtEncodingError("program has no blocks")
    check_supported_commands(program)

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
    dynamic_points = frozenset((row.block_id, row.cmd_index) for row in dsa.dynamic_assignments)
    symbol_sorts = _canonical_symbol_sorts(ctx.tac_file.symbol_sorts)
    inline_symbols_by_point = (
        _inline_static_symbols_by_point(program, du.definitions, set(dynamic_points), symbol_sorts)
        if ctx.inline_scalars
        else {}
    )
    vc = VCBuilder(_vc_config_for_sea(ctx))
    aliases = _define_reachability_aliases(vc, program, symbol_sorts, entry)
    aliases.update(
        {
            name: term(name, _sort_for(symbol_sorts=symbol_sorts, name=name))
            for name in inline_symbols_by_point.values()
        }
    )
    expr = TacExprLowerer(vc, symbol_sorts, symbol_aliases=aliases)
    return SeaEncodingState(
        ctx=ctx,
        program=program,
        du=du,
        dsa=dsa,
        vc=vc,
        expr=expr,
        entry=entry,
        symbol_sorts=symbol_sorts,
        aliases=aliases,
        dynamic_points=dynamic_points,
        inline_points=frozenset(inline_symbols_by_point),
    )


def _vc_config_for_sea(ctx: EncoderContext) -> VCConfig:
    return VCConfig(
        produce_unsat_cores=ctx.unsat_core,
        globalize_eligible_facts=not ctx.guard_statics,
        annotate_with_cmds=ctx.annotate_with_cmds,
        guard_axioms=ctx.guard_axioms,
        assertion_policy=AssertionPolicy(
            grouped_kinds=(
                frozenset({FactKind.DEF, FactKind.ASSUME, FactKind.RANGE})
                if ctx.guard_statics
                else frozenset()
            )
        ),
    )


def check_supported_commands(program: TacProgram) -> None:
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, _SUPPORTED_CMD_TYPES):
                continue
            kind = type(cmd).__name__
            head = getattr(cmd, "head", None)
            head_part = f", head={head!r}" if head else ""
            raise SmtEncodingError(
                f"unsupported command at {block.id}:{idx} ({kind}{head_part}): {cmd.raw!r}"
            )


def emit_static_blocks(state: SeaEncodingState, *, use_block_guards: bool = True) -> None:
    for block in Cfg(state.program).ordered_blocks():
        guard = _block_guard_term(state.vc, block.id, state.entry) if use_block_guards else true()
        with state.vc.block(block.id, guard=guard) as builder:
            i = 0
            while i < len(block.commands):
                if (block.id, i) in state.dynamic_points:
                    i += 1
                    continue
                havoc_range = _havoc_range_event(block, i)
                if havoc_range is not None:
                    cmd, lo, hi = havoc_range
                    lhs = _canon(cmd.lhs)
                    if lhs in state.expr.symbol_aliases:
                        i += 2
                        continue
                    x = state.vc.const(lhs, _sort_for(symbol_sorts=state.symbol_sorts, name=lhs))
                    state.expr.require_sort(x, Int, lhs)
                    state.vc.range(
                        x,
                        lo=lo,
                        hi=hi,
                        scope="current",
                        name=state.vc.auto_name("havoc_range", x.text),
                        placement=FactPlacement.ELIGIBLE_GLOBAL,
                    )
                    i += 2
                    continue
                cmd = block.commands[i]
                with state.vc.stmt(_stmt_id(cmd, i), cmd.raw):
                    emit_static_command(
                        state,
                        builder,
                        cmd,
                        block.id,
                        inline=(block.id, i) in state.inline_points,
                    )
                i += 1


def emit_static_command(
    state: SeaEncodingState,
    builder: BlockBuilder,
    cmd: TacCmd,
    block_id: str,
    *,
    inline: bool = False,
) -> None:
    vc = state.vc
    expr = state.expr
    if isinstance(cmd, AssignExpCmd):
        lhs_name = _canon(cmd.lhs)
        if _is_map(expr.symbol_sorts, lhs_name):
            _emit_map_def(vc, expr, cmd)
            return
        lhs = vc.const(lhs_name, _sort_for(symbol_sorts=expr.symbol_sorts, name=lhs_name))
        rhs = expr.lower_scalar(_peel_narrow(cmd.rhs) if inline else cmd.rhs)
        expr.require_assignment_sort(lhs, rhs, cmd.rhs)
        builder.def_(
            lhs,
            rhs,
            name=vc.auto_name("def", lhs.text),
            inline=inline,
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


def collect_dynamic_defs(
    state: SeaEncodingState,
    *,
    use_block_guards: bool = True,
) -> dict[str, tuple[DynamicDefCase, ...]]:
    vc = state.vc
    expr = state.expr
    by_id = state.program.block_by_id()
    rows_by_symbol: dict[str, list[DsaDynamicAssignment]] = defaultdict(list)
    for row in state.dsa.dynamic_assignments:
        sym = _canon(row.symbol)
        if _is_map(state.symbol_sorts, sym):
            raise SmtEncodingError("encoding 'sea' does not support dynamic bytemaps yet")
        rows_by_symbol[sym].append(row)

    block_pos = {b.id: i for i, b in enumerate(Cfg(state.program).ordered_blocks())}
    dynamic_defs: dict[str, tuple[DynamicDefCase, ...]] = {}
    for sym, sym_rows in sorted(rows_by_symbol.items()):
        cases: list[DynamicDefCase] = []
        for row in sorted(sym_rows, key=lambda r: block_pos.get(r.block_id, 10**9)):
            block = by_id[row.block_id]
            cmd = block.commands[row.cmd_index]
            guard = _block_guard_term(vc, row.block_id, state.entry) if use_block_guards else true()
            with (
                vc.block(row.block_id, guard=guard),
                vc.stmt(
                    _stmt_id(cmd, row.cmd_index),
                    row.raw,
                ),
            ):
                if isinstance(cmd, AssignExpCmd):
                    rhs = expr.lower_scalar(cmd.rhs)
                elif isinstance(cmd, AssignHavocCmd):
                    rhs = _fresh_havoc(
                        vc,
                        sym,
                        row.block_id,
                        row.cmd_index,
                        _sort_for(symbol_sorts=state.symbol_sorts, name=sym),
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
                    vc.const(sym, _sort_for(symbol_sorts=state.symbol_sorts, name=sym)),
                    rhs,
                    cmd.rhs if isinstance(cmd, AssignExpCmd) else sym,
                )
            cases.append(
                DynamicDefCase(
                    symbol=sym,
                    block_id=row.block_id,
                    cmd_index=row.cmd_index,
                    guard=guard,
                    rhs=rhs,
                )
            )
        dynamic_defs[sym] = tuple(cases)
    return dynamic_defs


def emit_dynamic_defs(
    state: SeaEncodingState,
    dynamic_defs: dict[str, tuple[DynamicDefCase, ...]],
    *,
    guarded: bool,
) -> None:
    for sym, cases in dynamic_defs.items():
        state.vc.dynamic_def(
            state.vc.const(sym, _sort_for(symbol_sorts=state.symbol_sorts, name=sym)),
            tuple((case.guard, case.rhs) for case in cases),
            guarded=guarded,
        )


def emit_cfg(state: SeaEncodingState, cfg_encoding: str) -> None:
    symbol_terms = {name: alias.smt() for name, alias in state.aliases.items()}
    cfg_input = build_cfg_input(
        state.program,
        entry_block_id=state.entry,
        symbol_term=symbol_terms,
    )
    cfg_encoder = CFG_ENCODERS.get(cfg_encoding)
    if cfg_encoder is None:
        raise SmtEncodingError(
            f"unknown cfg_encoding {cfg_encoding!r}; available: {', '.join(sorted(CFG_ENCODERS))}"
        )
    cfg_constraints: list[str] = []
    cfg_emit = CfgEmit(
        add_constraint=cfg_constraints.append,
        add_decl=lambda name, sort: state.vc.const(name, Bool if sort == "Bool" else Int),
    )
    cfg_encoder(cfg_input, cfg_emit)
    if cfg_constraints:
        state.vc.section("cfg constraints")
        for raw in cfg_constraints:
            state.vc.raw_fact(raw, origin="cfg")


def emit_assert_objective(state: SeaEncodingState, ctx: EncoderContext) -> None:
    assert_block_guard = _block_guard_term(state.vc, ctx.assert_site.block_id, state.entry)
    with state.vc.block(ctx.assert_site.block_id, guard=assert_block_guard):
        pred = state.expr.lower_bool(ctx.assert_site.command.predicate)
    state.vc.assert_failure_objective(state.vc.const("BLK_EXIT", Bool), assert_block_guard, pred)


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


def _emit_map_def(vc: VCBuilder, expr: TacExprLowerer, cmd: AssignExpCmd) -> None:
    lhs = _canon(cmd.lhs)
    vc.bytemap.define(lhs, lambda idx: _lower_map_body(expr, cmd.rhs, idx, lhs))


def _inline_static_symbols_by_point(
    program: TacProgram,
    definitions: tuple[DefinitionSite, ...],
    dynamic_points: set[tuple[str, int]],
    symbol_sorts: dict[str, str],
) -> dict[tuple[str, int], str]:
    jumpi_conditions = {
        _canon(cmd.condition)
        for block in program.blocks
        for cmd in block.commands
        if isinstance(cmd, JumpiCmd)
    }
    by_id = program.block_by_id()
    out: dict[tuple[str, int], str] = {}
    for site in definitions:
        point = (site.block_id, site.cmd_index)
        if point in dynamic_points:
            continue
        if site.symbol in jumpi_conditions:
            continue
        if _is_map(symbol_sorts, site.symbol):
            continue
        if _sort_for(symbol_sorts=symbol_sorts, name=site.symbol) is not Int:
            continue
        cmd = by_id[site.block_id].commands[site.cmd_index]
        if not isinstance(cmd, AssignExpCmd):
            continue
        if _is_inlinable_rhs(cmd.rhs):
            out[point] = site.symbol
    return out


def _peel_narrow(expr: TacExpr) -> TacExpr:
    while (
        isinstance(expr, ApplyExpr)
        and expr.op == "Apply"
        and len(expr.args) == 2
        and isinstance(expr.args[0], SymbolRef)
        and expr.args[0].name.startswith("safe_math_narrow_bv")
        and expr.args[0].name.endswith(":bif")
    ):
        expr = expr.args[1]
    return expr


def _is_inlinable_rhs(expr: TacExpr) -> bool:
    expr = _peel_narrow(expr)
    if isinstance(expr, SymbolRef):
        return True
    if isinstance(expr, ConstExpr):
        return expr.value.strip() not in {"true", "false"}
    if isinstance(expr, ApplyExpr) and len(expr.args) == 2:
        if expr.op in _INLINE_LINEAR_OPS or expr.op in _INLINE_LINEAR_SCALE_OPS:
            return any(isinstance(arg, ConstExpr) for arg in expr.args) and all(
                isinstance(arg, (ConstExpr, SymbolRef)) for arg in expr.args
            )
    return False


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


def _stmt_id(cmd: TacCmd, index: int) -> str | int:
    return cmd.meta_index if cmd.meta_index is not None else index
