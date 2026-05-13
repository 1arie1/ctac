from __future__ import annotations

from dataclasses import dataclass

from ctac.ast.nodes import AssertCmd
from ctac.smt.cfg import CFG_ENCODERS, CfgEmit, CfgEncodeInput, build_cfg_input
from ctac.smt.encoding.base import EncoderContext, SmtEncoder, SmtEncodingError
from ctac.smt.encoding.sea import (
    DynamicDefCase,
    SeaEncodingState,
    _sort_for,
    collect_dynamic_defs,
    emit_static_blocks,
    prepare_sea_state,
)
from ctac.smt.vc.config import FactKind
from ctac.smt.vc.lowering import LeinoEdge, LeinoLowerer
from ctac.smt.vc.script import VCScript
from ctac.smt.vc.terms import Bool, Int, Term, eq, term, true


@dataclass
class LeinoEncoder(SmtEncoder):
    name: str = "leino"

    def encode(self, ctx: EncoderContext) -> VCScript:
        self._reject_unsupported_options(ctx)
        state = prepare_sea_state(ctx)
        emit_static_blocks(state, use_block_guards=False)
        dynamic_defs = collect_dynamic_defs(state, use_block_guards=False)
        emit_terminal_dynamic_premises(state, dynamic_defs)
        emit_assert_fact(state, ctx)

        edges = leino_edges(state, dynamic_defs)
        state.vc.config.fact_lowerer = LeinoLowerer(
            entry_block=state.entry,
            edges=edges,
        )
        if needs_cfg_constraints(state):
            emit_cfg_constraints(state, ctx.cfg_encoding)
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
            raise SmtEncodingError(
                f"encoding 'leino' does not support {', '.join(unsupported)} yet"
            )


def emit_assert_fact(state: SeaEncodingState, ctx: EncoderContext) -> None:
    cmd = ctx.assert_site.command
    if not isinstance(cmd, AssertCmd):
        raise SmtEncodingError("validated assert site is not an AssertCmd")
    with state.vc.block(ctx.assert_site.block_id, guard=true()) as builder:
        with state.vc.stmt(ctx.assert_site.cmd_index, cmd.raw):
            builder.assert_(state.expr.lower_bool(cmd.predicate))


def leino_edges(
    state: SeaEncodingState,
    dynamic_defs: dict[str, tuple[DynamicDefCase, ...]],
) -> tuple[LeinoEdge, ...]:
    cfg_input = _build_cfg_input(state)
    dynamic_premises = _dynamic_premises_by_block(state, dynamic_defs)
    edges: list[LeinoEdge] = []
    for edge in cfg_input.edges:
        source = cfg_input.block_ids[edge.pred]
        target = cfg_input.block_ids[edge.succ]
        edges.append(
            LeinoEdge(
                source=source,
                target=target,
                condition=term(edge.branch_cond, Bool),
                premises=dynamic_premises.get(source, ()),
            )
        )
    return tuple(edges)


def _dynamic_premises_by_block(
    state: SeaEncodingState,
    dynamic_defs: dict[str, tuple[DynamicDefCase, ...]],
) -> dict[str, tuple[Term, ...]]:
    by_block: dict[str, list[Term]] = {}
    for sym, cases in dynamic_defs.items():
        lhs = state.vc.const(sym, _sort_for(symbol_sorts=state.symbol_sorts, name=sym))
        for case in cases:
            by_block.setdefault(case.block_id, []).append(eq(lhs, case.rhs))
    return {block_id: tuple(premises) for block_id, premises in by_block.items()}


def emit_terminal_dynamic_premises(
    state: SeaEncodingState,
    dynamic_defs: dict[str, tuple[DynamicDefCase, ...]],
) -> None:
    cfg_input = _build_cfg_input(state)
    terminal_blocks = {
        cfg_input.block_ids[i] for i in range(len(cfg_input.block_ids)) if not cfg_input.succs_of(i)
    }
    for sym, cases in dynamic_defs.items():
        lhs = state.vc.const(sym, _sort_for(symbol_sorts=state.symbol_sorts, name=sym))
        for case in cases:
            if case.block_id not in terminal_blocks:
                continue
            with state.vc.block(case.block_id, guard=true()):
                state.vc.fact(
                    FactKind.DEF,
                    eq(lhs, case.rhs),
                    name=state.vc.auto_name("dynamic_def", lhs.text),
                    origin="dynamic-def",
                )


def needs_cfg_constraints(state: SeaEncodingState) -> bool:
    return bool(state.aliases)


def emit_cfg_constraints(state: SeaEncodingState, cfg_encoding: str) -> None:
    cfg_input = _build_cfg_input(state)
    for guard in cfg_input.block_guards:
        if guard != "true":
            state.vc.const(guard, Bool)
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
    for raw in cfg_constraints:
        state.vc.raw_fact(raw, kind=FactKind.CFG, origin="cfg")


def _build_cfg_input(state: SeaEncodingState) -> CfgEncodeInput:
    symbol_terms = {name: alias.smt() for name, alias in state.aliases.items()}
    return build_cfg_input(
        state.program,
        entry_block_id=state.entry,
        symbol_term=symbol_terms,
    )
