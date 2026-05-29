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
    is_reachability_var,
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
        coi = compute_coi_defs(state, ctx, mode=ctx.coi)
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

    # Branch-condition booleans are referenced by the gates and the CFG
    # constraints regardless of COI, so declare them all. Each is *defined*
    # (its equality emitted) only when emit_static_blocks keeps it (the
    # condition is in the COI because it gates a kept phi); otherwise it
    # stays a free boolean. A branch that gates no kept phi can be left
    # free soundly — the CFG just explores both edges, which yield the
    # same asserted value.
    for bc in bcs.values():
        if bc.cond in ("true", "false") or bc.cond in state.vc.define_funs:
            continue
        state.vc.const(bc.cond, Bool)
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


def compute_coi_defs(
    state: SeaEncodingState, ctx: EncoderContext, *, mode: str = "thin"
) -> frozenset[ProgramPoint]:
    """Cone of influence: the definition points to emit.

    ``thin`` (default): seed the assert and every ``assume`` only; the
    backward data closure (reaching-defs) pulls what feeds them.
    Definitions feeding none of these — the bytemap Store-chains /
    arithmetic irrelevant to the assertion — drop. Branch conditions are
    NOT seeded wholesale: they are declared unconditionally (in
    ``_install_gates``) and may stay free booleans. The only ones we must
    *define* are those a **kept phi gates on** — otherwise a free gate
    could pick the wrong arm and diverge from ``sea`` — so on reaching a
    phi we ``need_gate`` its gate block and pull the branch conditions of
    that block's transitive control-dependence controllers (virtual phi:
    kept DSA case at ``b`` -> ``need_gate(b)``; materialized: a use of
    ``ReachabilityCertora_k`` -> ``need_gate(k)``). Static defs are
    single-def and dominated, so their values are fixed by the objective
    regardless of branch values; they need no path conditions.

    ``coarse``: additionally seed every branch condition (``JumpiCmd``) and
    walk control-dependence on every kept block, keeping all branch cones.
    Prunes less; a conservative fallback.

    ``aggressive``: seed the assert ONLY (not all assumes); an ``assume`` is
    kept only when it shares a variable with the assert's cone (transitively
    — a kept assume's own variables join the cone and may pull more
    assumes). Assumes over disjoint variables drop. This is NOT verdict-
    equivalent to ``sea``: dropping assumes *widens* the model set, so it is
    **sound only for UNSAT** (an UNSAT result proves the full VC; a SAT may
    be spurious). A proof obstruction — useful when assume mass obstructs z3.
    """
    coarse = mode == "coarse"
    aggressive = mode == "aggressive"
    program = state.program
    rd = analyze_reaching_definitions(program, def_use=state.du)
    cd = analyze_control_dependence(program)
    term_idx = {b.id: len(b.commands) - 1 for b in program.blocks if b.commands}
    by_id = program.block_by_id()
    block_ids = set(by_id)

    selected: set[ProgramPoint] = set()
    work: deque[ProgramPoint] = deque()

    def add(pt: ProgramPoint) -> None:
        if pt not in selected:
            selected.add(pt)
            work.append(pt)

    gate_needed: set[str] = set()

    def need_gate(start: str) -> None:
        # `start` and its transitive controllers have gates that reference
        # those controllers' branch conditions; pull each condition's def.
        stack = [start]
        while stack:
            blk = stack.pop()
            if blk in gate_needed or blk not in block_ids:
                continue
            gate_needed.add(blk)
            for ctrl in cd.controllers.get(blk, ()):
                last = term_idx.get(ctrl)
                if last is not None:
                    add(ProgramPoint(ctrl, last))
                stack.append(ctrl)

    # In aggressive mode assumes are not seeded; they are pulled in only
    # when they share a variable with the cone. Index them by used symbol.
    assumes_by_sym: dict[str, list[ProgramPoint]] = {}
    if aggressive:
        for block in program.blocks:
            for idx, cmd in enumerate(block.commands):
                if isinstance(cmd, AssumeExpCmd):
                    apt = ProgramPoint(block.id, idx)
                    for sym in command_uses(cmd):
                        assumes_by_sym.setdefault(sym, []).append(apt)

    add(ProgramPoint(ctx.assert_site.block_id, ctx.assert_site.cmd_index))
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if (isinstance(cmd, AssumeExpCmd) and not aggressive) or (
                coarse and isinstance(cmd, JumpiCmd)
            ):
                add(ProgramPoint(block.id, idx))

    while work:
        pt = work.popleft()
        block = by_id.get(pt.block_id)
        if block is None or not (0 <= pt.cmd_index < len(block.commands)):
            continue
        cmd = block.commands[pt.cmd_index]
        if coarse:
            for ctrl in cd.controllers.get(pt.block_id, ()):
                last = term_idx.get(ctrl)
                if last is not None:
                    add(ProgramPoint(ctrl, last))
        elif (pt.block_id, pt.cmd_index) in state.dynamic_points:
            need_gate(pt.block_id)
        in_here = rd.in_by_command.get(pt, {})
        for sym in command_uses(cmd):
            if not coarse and is_reachability_var(sym):
                k = block_id_for_reachability_var(sym)
                if k is not None:
                    need_gate(k)
            if aggressive:
                for apt in assumes_by_sym.get(sym, ()):
                    add(apt)
            for ds in in_here.get(sym, ()):
                add(ProgramPoint(ds.block_id, ds.cmd_index))
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
