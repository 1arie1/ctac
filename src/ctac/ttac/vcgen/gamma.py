"""Thin-gamma planning for the sea_gate-style vcgen mode.

Computes, per scalar phi site, the total-gamma certificate the Lean
checker (``Ttac.checkVCGAnn``) validates: structured cases (parent
gate + oriented branch), the materialized gate table, and the
valuation table. Shared by the encoder (which renders the gamma
constraint into the smt2) and the annotator (which serializes the
certificates), so the emitted constraint and the checker's rebuilt
anchor match by construction.

Everything here is untrusted: a wrong plan either fails the local
mirror checks below (the site falls back to the classical ``phiRhs``
constraint) or is rejected by the Lean checker (build failure) — never
unsound.

The construction is deliberately conservative. A case's committing
branch is found by climbing single-predecessor, single-successor
pass-through chains from the join's predecessor; the climb guarantees
the postdominator side condition the checker re-derives (every block
on the chain has one successor, so all paths from the branch target
reach the join). Sites the climb cannot handle keep the classical
constraint.
"""

from __future__ import annotations

from dataclasses import dataclass, field

import networkx as nx

from ctac.ttac import ast
from ctac.ttac.analysis import cfg as ttac_cfg
from ctac.ttac.ast import Ty

from ..lean.vc_expected import TRUE, mk_and2, mk_ite_b, mk_ite_i, mk_not, mk_or

Term = tuple


@dataclass(frozen=True)
class GateRowPlan:
    parent: int | None  # gate-table index; None = controller dominates aB
    ctrl: str
    side: bool


@dataclass(frozen=True)
class GatePlan:
    block: str
    rows: tuple[GateRowPlan, ...]


@dataclass(frozen=True)
class GammaCasePlan:
    row: GateRowPlan
    src: str  # arm value name
    covers: tuple[str, ...]  # covered predecessor labels


@dataclass(frozen=True)
class GammaPlan:
    sites: dict[tuple[str, int], tuple[GammaCasePlan, ...]] = field(
        default_factory=dict
    )
    gates: tuple[GatePlan, ...] = ()
    val: dict[str, tuple[tuple[str, bool], ...]] = field(default_factory=dict)


class _PlanFail(Exception):
    pass


def _edge_claims(blocks, p: str, b: str) -> frozenset[tuple[str, bool]]:
    """Mirror of the Lean ``edgeClaims``: the branch-register value the
    edge ``p -> b`` itself determines."""
    term = blocks[p].terminator
    if isinstance(term, ast.IfGoto):
        t, e = term.then_target, term.else_target
        if b == t and b != e:
            return frozenset({(term.cond, True)})
        if b == e and b != t:
            return frozenset({(term.cond, False)})
    return frozenset()


def _val_table(program: ast.Program, blocks, preds) -> dict[str, frozenset]:
    """Maximal closure-valid claim table: forward dataflow with
    intersection at merges, seeded by edge determinations."""
    claims: dict[str, frozenset] = {}
    for label in ttac_cfg.topo_order(program):
        ps = preds.get(label, [])
        if label == program.entry or not ps:
            claims[label] = frozenset()
            continue
        per_pred = [
            claims.get(q, frozenset()) | _edge_claims(blocks, q, label)
            for q in ps
        ]
        acc = per_pred[0]
        for s in per_pred[1:]:
            acc = acc & s
        claims[label] = acc
    return claims


def plan_gammas(program: ast.Program, types: dict[str, Ty]) -> GammaPlan:
    sites_asserts = [
        b.label
        for b in program.blocks
        for c in b.commands
        if isinstance(c, ast.Assert)
    ]
    if len(sites_asserts) != 1:
        return GammaPlan()
    assert_block = sites_asserts[0]

    g = ttac_cfg.to_digraph(program)
    blocks = ttac_cfg.block_by_label(program)
    preds = ttac_cfg.predecessors(program)
    index = {b.label: i for i, b in enumerate(program.blocks)}
    entry = program.entry
    if entry is None or not nx.is_directed_acyclic_graph(g):
        return GammaPlan()

    idom = nx.immediate_dominators(g, entry)
    try:
        ipdom = nx.immediate_dominators(g.reverse(copy=True), assert_block)
    except nx.NetworkXError:
        return GammaPlan()

    def _tree_dominates(tree, a: str, b: str) -> bool:
        cur = b
        while True:
            if cur == a:
                return True
            nxt = tree.get(cur)
            if nxt is None or nxt == cur:
                return False
            cur = nxt

    def dominates(a: str, b: str) -> bool:
        return _tree_dominates(idom, a, b)

    def pdominates(a: str, b: str) -> bool:
        """``a`` postdominates ``b`` toward the assert block (missing
        entries — blocks not reaching it — count as not dominated;
        conservative vs the Lean table's ⊤ there)."""
        return b in ipdom and _tree_dominates(ipdom, a, b)

    claims = _val_table(program, blocks, preds)

    def commit(p: str, j: str) -> tuple[str, bool]:
        """The branch that commits execution to the arrival at ``j``
        via ``p``: the nearest dominating branch whose taken side is
        pinned in ``p``'s claims and postdominated by ``j`` toward the
        assert block — the facts the Lean checker re-derives for the
        selection and forcing directions respectively."""
        cl = claims.get(p, frozenset()) | _edge_claims(blocks, p, j)
        d: str | None = p
        while d is not None:
            term = blocks[d].terminator
            if isinstance(term, ast.IfGoto) and term.then_target != term.else_target:
                for side in (True, False):
                    s = term.then_target if side else term.else_target
                    if (
                        (term.cond, side) in cl
                        and index[s] <= index[assert_block]
                        and pdominates(j, s)
                    ):
                        return d, side
            nxt = idom.get(d)
            if nxt is None or nxt == d:
                break
            d = nxt
        raise _PlanFail

    gates: list[GatePlan] = []
    gate_memo: dict[str, int | None] = {}

    def gate_of(label: str) -> int | None:
        if label in gate_memo:
            return gate_memo[label]
        if dominates(label, assert_block):
            gate_memo[label] = None
            return None
        rows: list[GateRowPlan] = []
        for pr in sorted(preds.get(label, []), key=index.__getitem__):
            c, side = commit(pr, label)
            rows.append(GateRowPlan(gate_of(c), c, side))
        if not rows:
            raise _PlanFail
        gate = GatePlan(label, tuple(rows))
        gates.append(gate)
        gate_memo[label] = len(gates) - 1
        return gate_memo[label]

    def _mk_row(c: str, side: bool) -> GateRowPlan:
        return GateRowPlan(gate_of(c), c, side)

    # three-valued mirrors of the Lean forcing/selection checks, used
    # only to decide emission (the checker re-verifies everything)
    def row_val3(row: GateRowPlan, cl: frozenset) -> bool | None:
        cond = blocks[row.ctrl].terminator.cond
        if (cond, row.side) in cl:
            o: bool | None = True
        elif (cond, not row.side) in cl:
            o = False
        else:
            o = None
        p = True if row.parent is None else gate_val3(row.parent, cl)
        if p is False or o is False:
            return False
        if p is True and o is True:
            return True
        return None

    def gate_val3(i: int, cl: frozenset) -> bool | None:
        vals = [row_val3(r, cl) for r in gates[i].rows]
        if any(v is True for v in vals):
            return True
        if all(v is False for v in vals):
            return False
        return None

    def arm_src_for(arms, p: str) -> str:
        for arm in arms:
            if arm.label == p:
                return arm.value
        return arms[-1].value

    def selection_ok(j: str, arms, cases: list[GammaCasePlan]) -> bool:
        for p in preds.get(j, []):
            cl = claims.get(p, frozenset()) | _edge_claims(blocks, p, j)
            es = arm_src_for(arms, p)
            for case in cases:
                v = row_val3(case.row, cl)
                if p in case.covers:
                    if case.src != es or v is not True:
                        return False
                    break
                if v is not False:
                    return False
        return True

    plan_sites: dict[tuple[str, int], tuple[GammaCasePlan, ...]] = {}
    for block in program.blocks:
        for i, cmd in enumerate(block.commands):
            if not isinstance(cmd, ast.Phi):
                continue
            if types.get(cmd.target.name) is Ty.BYTEMAP:
                continue
            if len(cmd.arms) < 2:
                continue
            checkpoint = len(gates)
            memo_snapshot = dict(gate_memo)
            try:
                cases = [
                    GammaCasePlan(
                        _mk_row(*commit(arm.label, block.label)),
                        arm.value,
                        (arm.label,),
                    )
                    for arm in cmd.arms[:-1]
                ]
            except _PlanFail:
                del gates[checkpoint:]
                gate_memo.clear()
                gate_memo.update(memo_snapshot)
                continue
            if not selection_ok(block.label, cmd.arms, cases):
                del gates[checkpoint:]
                gate_memo.clear()
                gate_memo.update(memo_snapshot)
                continue
            plan_sites[(block.label, i)] = tuple(cases)

    if not plan_sites:
        return GammaPlan()
    val = {
        label: tuple(sorted(cl)) for label, cl in claims.items() if cl
    }
    return GammaPlan(sites=plan_sites, gates=tuple(gates), val=val)


# ------------------------------------------------------------------------
# Term construction: exact mirrors of the Lean generators, parametrized
# over the atom payloads (names for the encoder, register numbers for
# the annotator) so both sides fold identically.
# ------------------------------------------------------------------------


def gate_term(gates, i: int, cond_atom, blocks) -> Term:
    """Mirror of ``Vc.gateExpGo``: ``mkOr`` over the row expressions."""
    return mk_or([row_term(gates, r, cond_atom, blocks) for r in gates[i].rows])


def row_term(gates, row: GateRowPlan, cond_atom, blocks) -> Term:
    """Mirror of ``Vc.rowExp``: ``parent ∧ orient`` (parent first)."""
    cond = blocks[row.ctrl].terminator.cond
    orient = cond_atom(cond) if row.side else mk_not(cond_atom(cond))
    if row.parent is None:
        return orient
    return mk_and2(gate_term(gates, row.parent, cond_atom, blocks), orient)


def tgamma_rhs_term(
    cases,
    arms,
    gates,
    blocks,
    *,
    is_int: bool,
    var_atom,
    cond_atom,
    guard_atom,
) -> Term:
    """Mirror of ``Vc.gammaExpT?``: the case ITE chain over the
    ``phiRhs`` tail (itself the mirror of ``Vc.phiChain``)."""
    mk_ite = mk_ite_i if is_int else mk_ite_b
    tail: Term = var_atom(arms[-1].value)
    for arm in reversed(arms[:-1]):
        tail = mk_ite(guard_atom(arm.label), var_atom(arm.value), tail)
    out = tail
    for case in reversed(cases):
        out = mk_ite(
            row_term(gates, case.row, cond_atom, blocks),
            var_atom(case.src),
            out,
        )
    return out


def term_to_smt(t: Term) -> str:
    """Render a name-payload term back to SMT-LIB text."""
    kind = t[0]
    if kind == "litI":
        n = t[1]
        return str(n) if n >= 0 else f"(- {-n})"
    if kind == "litb":
        return "true" if t[1] else "false"
    if kind == "sym":
        return t[1]
    ops = {
        "add": "+", "sub": "-", "mul": "*", "div": "div",
        "le": "<=", "lt": "<", "eqI": "=", "eqB": "=",
        "and": "and", "or": "or", "imp": "=>", "not": "not", "ite": "ite",
    }
    args = " ".join(term_to_smt(a) for a in t[1:])
    return f"({ops[kind]} {args})"


def encoder_atoms(entry: str, sanitize):
    """Name-payload atom builders for the encoder's smt rendering."""

    def var_atom(name: str) -> Term:
        return ("sym", name)

    def cond_atom(name: str) -> Term:
        return ("sym", name)

    def guard_atom(label: str) -> Term:
        if label == entry:
            return TRUE
        return ("sym", "BLK_" + sanitize(label))

    return var_atom, cond_atom, guard_atom
