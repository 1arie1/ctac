from __future__ import annotations

from collections import OrderedDict, deque
from dataclasses import dataclass, replace
from typing import Callable

from ctac.analysis import analyze_control_dependence, analyze_reaching_definitions
from ctac.analysis.expr_walk import command_uses
from ctac.analysis.model import ProgramPoint
from ctac.ast.nodes import AssumeExpCmd, JumpiCmd
from ctac.smt.encoding.base import EncoderContext, SmtEncoder, SmtEncodingError
from ctac.smt.encoding.path_skeleton import (
    block_id_for_reachability_var,
    branch_conditions,
    sanitize_ident,
)
from ctac.smt.encoding.sea import (
    DynamicDefCase,
    SeaEncodingState,
    collect_dynamic_defs,
    emit_assert_objective,
    emit_cfg,
    emit_dynamic_defs,
    emit_static_blocks,
    prepare_sea_state,
)
from ctac.smt.vc.script import DefineFun, VCScript
from ctac.smt.vc.terms import Bool, Term, and_, not_, or_, term, true


@dataclass
class SeaGateEncoder(SmtEncoder):
    name: str = "sea_gate"

    def encode(self, ctx: EncoderContext) -> VCScript:
        self._reject_unsupported_options(ctx)
        state = prepare_sea_state(ctx)
        gate = _install_gates(state)
        coi = compute_coi_defs(state, ctx)
        emit_static_blocks(state, keep=lambda b, i: ProgramPoint(b, i) in coi)
        dynamic_defs = _filter_dynamic(_collect_gate_dynamic_defs(state, gate), coi)
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
            raise SmtEncodingError(
                f"encoding 'sea_gate' does not support {', '.join(unsupported)} yet"
            )


def _gate_name(block_id: str) -> str:
    return f"gate_{sanitize_ident(block_id)}"


def _install_gates(state: SeaEncodingState) -> Callable[[str], Term]:
    """Build CD-minimal reach gates and re-gate the phi seams.

    For each block ``k``, ``gate(k) = OR over controllers c of (gate(c) AND
    orient(c -> k))`` — the thinned reach condition over *branch conditions*
    (control dependence), globally equal to ``BLK_k`` under the CFG
    constraints but expressed only over the deciding branches. Emitted as
    ``(define-fun gate_<bid> () Bool ...)`` in ascending topo order so each
    referenced ``gate_<controller>`` is already defined.

    SEAM 1 (materialized phi): the ``ReachabilityCertora_k`` aliases (set up
    by ``prepare_sea_state`` to ``BLK_k``) are retargeted to ``gate(k)``, so
    every ``Ite(RC_k, ...)`` in scalar and bytemap defs inherits the
    branch-condition gate with no change to the lowerer.

    Returns ``gate(block_id) -> Term`` for SEAM 2 (virtual phi guards).
    """
    program = state.program
    cd = analyze_control_dependence(program)
    aliases_smt = {name: alias.smt() for name, alias in state.aliases.items()}
    bcs = branch_conditions(program, symbol_term_by_name=aliases_smt)
    postdom = cd.postdominators
    block_ids = {b.id for b in program.blocks}

    def gate_ref(block_id: str) -> Term:
        return term(_gate_name(block_id), Bool)

    # Blocks needing a gate define-fun: RC-alias targets and dynamic-def
    # blocks, closed under control dependence (each gate references its
    # controllers' gates).
    needed: set[str] = set()
    for name in state.aliases:
        bid = block_id_for_reachability_var(name)
        if bid is not None and bid in block_ids:
            needed.add(bid)
    for row in state.dsa.dynamic_assignments:
        needed.add(row.block_id)
    work = list(needed)
    while work:
        for ctrl in cd.controllers.get(work.pop(), ()):
            if ctrl not in needed:
                needed.add(ctrl)
                work.append(ctrl)

    def orient(ctrl: str, dep: str) -> Term:
        bc = bcs.get(ctrl)
        if bc is None:
            raise SmtEncodingError(
                f"control-dependence controller {ctrl!r} of {dep!r} has no branch condition"
            )
        cond = term(bc.cond, Bool)
        if dep in postdom.get(bc.then_target, ()):
            return cond
        if dep in postdom.get(bc.else_target, ()):
            return not_(cond)
        raise SmtEncodingError(f"cannot orient control-dependence edge {ctrl!r} -> {dep!r}")

    def gate_body(dep: str) -> Term:
        ctrls = cd.controllers.get(dep, ())
        if not ctrls:
            return true()
        return or_(*(and_(gate_ref(c), orient(c, dep)) for c in ctrls))

    gate_defs: OrderedDict[str, DefineFun] = OrderedDict()
    for bid in sorted(needed, key=lambda b: cd.topo_index.get(b, 0)):
        name = _gate_name(bid)
        gate_defs[name] = DefineFun(name, (), Bool, gate_body(bid))

    # Gates first (topo order), then the existing define-funs with the RC
    # aliases retargeted to reference their gate.
    rebuilt: OrderedDict[str, DefineFun] = OrderedDict(gate_defs)
    for name, df in state.vc.define_funs.items():
        bid = block_id_for_reachability_var(name)
        if bid is not None and bid in needed:
            rebuilt[name] = DefineFun(name, (), Bool, gate_ref(bid))
        else:
            rebuilt[name] = df
    state.vc.define_funs = rebuilt
    return gate_ref


def _collect_gate_dynamic_defs(
    state: SeaEncodingState, gate: Callable[[str], Term]
) -> dict[str, tuple[DynamicDefCase, ...]]:
    """SEAM 2: re-gate virtual-phi (DSA-merge) cases on branch conditions.

    ``collect_dynamic_defs`` gates each case on its defining block's ``BLK_b``;
    replace that with ``gate(b)`` so the synthesized merge selects on branch
    conditions like the materialized phis.
    """
    dynamic_defs = collect_dynamic_defs(state)
    return {
        sym: tuple(replace(case, guard=gate(case.block_id)) for case in cases)
        for sym, cases in dynamic_defs.items()
    }


def compute_coi_defs(state: SeaEncodingState, ctx: EncoderContext) -> frozenset[ProgramPoint]:
    """Cone of influence: the definition points to emit.

    Seeded by the assert, every ``assume``, and every branch condition
    (``JumpiCmd``) — the latter because the control plane (CFG constraints)
    and the gates reference branch-condition symbols of *all* blocks, so
    those defs must stay defined. The backward closure over data
    (reaching-defs) and control (control-dependence controllers) then pulls
    in exactly what feeds them. Definitions feeding none of these — the
    bytemap Store-chains / arithmetic irrelevant to the assertion — drop.

    Traversal through both phi kinds is automatic: a materialized
    ``Ite(RC_k, a, b)`` exposes ``a``/``b`` and ``RC_k`` via ``command_uses``;
    a virtual (DSA-merge) symbol's uses resolve through reaching-defs to its
    case sites, and control-dependence closure on each case block keeps that
    case's synthesized gate conditions.
    """
    program = state.program
    rd = analyze_reaching_definitions(program, def_use=state.du)
    cd = analyze_control_dependence(program)
    term_idx = {b.id: len(b.commands) - 1 for b in program.blocks if b.commands}
    by_id = program.block_by_id()

    seeds: list[ProgramPoint] = [
        ProgramPoint(ctx.assert_site.block_id, ctx.assert_site.cmd_index)
    ]
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, (AssumeExpCmd, JumpiCmd)):
                seeds.append(ProgramPoint(block.id, idx))

    selected: set[ProgramPoint] = set(seeds)
    work: deque[ProgramPoint] = deque(dict.fromkeys(seeds))
    while work:
        pt = work.popleft()
        block = by_id.get(pt.block_id)
        if block is None or not (0 <= pt.cmd_index < len(block.commands)):
            continue
        cmd = block.commands[pt.cmd_index]
        in_here = rd.in_by_command.get(pt, {})
        for sym in command_uses(cmd):
            for ds in in_here.get(sym, ()):
                cand = ProgramPoint(ds.block_id, ds.cmd_index)
                if cand not in selected:
                    selected.add(cand)
                    work.append(cand)
        for ctrl in cd.controllers.get(pt.block_id, ()):
            last = term_idx.get(ctrl)
            if last is None:
                continue
            cand = ProgramPoint(ctrl, last)
            if cand not in selected:
                selected.add(cand)
                work.append(cand)
    return frozenset(selected)


def _filter_dynamic(
    dynamic_defs: dict[str, tuple[DynamicDefCase, ...]],
    coi: frozenset[ProgramPoint],
) -> dict[str, tuple[DynamicDefCase, ...]]:
    """Keep a virtual phi all-or-nothing: drop a symbol only if none of its
    case sites is in the cone of influence."""
    return {
        sym: cases
        for sym, cases in dynamic_defs.items()
        if any(ProgramPoint(c.block_id, c.cmd_index) in coi for c in cases)
    }
