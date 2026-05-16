"""Recognize and reverse the upstream pipeline's pre-purified
``Div`` shape.

Some Certora outputs arrive with division pre-axiomatized in the
Euclidean form::

    AssignHavocCmd Q
    AssignExpCmd P1 IntMul(Q, B)
    [AssignExpCmd <tmp> ...]*              # 0+ intermediate A bindings
    AssignExpCmd P3 Le(P1, A_term)         # Q*B <= A
    AssumeCmd P3 "Division purification"
    AssignExpCmd P4 IntAdd(Q, 0x1)
    AssignExpCmd P5 IntMul(P4, B)
    AssignExpCmd P6 Gt(P5, A_term)         # (Q+1)*B > A
    AssumeCmd P6 "Division purification"

The Euclidean conjunction is equivalent to
``B > 0 ∧ Q = floor(A / B)``: when ``B = 0``, ``B*Q ≤ A`` gives
``0 ≤ A`` (true) and ``A < B*(Q+1)`` gives ``A < 0`` (false on
non-negative ``A``), so the conjunction is infeasible and kills
the path. SMT integer division has a defined value at zero
(z3 returns ``0``), so recovering only ``IntDiv`` would lose the
``B=0`` infeasibility and admit new SAT models. The pass emits an
explicit ``assume Gt(B, 0)`` alongside the recovered division to
keep that semantics.

This pass walks every block and folds the pattern into two cmds:
``assume Gt(B, 0)`` at the original havoc slot, and
``Q = narrow(IntDiv(A_term, B))`` at the slot the ``Le`` cmd
held — so any intermediate ``A`` bindings still dominate the
new use of ``A_term``. The ``narrow`` wrap is the standard
type-assertion that lifts the int-domain ``IntDiv`` result back
to ``bv256`` (matching ``Q``'s declared sort, analogous to
``R6_CEILDIV``'s emission of ``narrow(IntCeilDiv(...))``).

Subsequent rules see the natural ``IntDiv`` shape: e.g.
``MUL_DIV_TO_MULDIV`` recognizes ``IntDiv(IntMul(a, b), c)`` and
lifts to ``IntMulDiv``, which the sea encoder axiomatizes
directly. The intermediate ``A`` bindings that survive after the
rewrite are cleaned up by DCE if unreferenced.

Running once at the very start of ``ctac rw`` lets the rest of
the pipeline see the natural ``Div`` shape, so our own
``R4A_DIV_PURIFY`` (gated by ``--purify-div``) becomes the single
authority on division purification — no churn from re-purifying
upstream's tmps.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.trail import Substitution
from ctac.rewrite.unparse import canonicalize_cmd


_TMP_PREFIX = "tacTmp!div"
_ZERO_INT = ConstExpr("0x0(int)")


@dataclass(frozen=True)
class UnpurifyResult:
    """Outcome of :func:`unpurify_div`.

    ``program`` is the rewritten program. ``hits`` is the count of
    purification patterns recognized (one per division).
    ``substitutions`` records each recovered Q-as-IntDiv so
    ``ctac run --model`` can replay the original program — at the
    original's still-present ``Q = havoc``, the trail evaluates the
    IntDiv expression against the model's surviving values.
    """

    program: TacProgram
    hits: int
    substitutions: tuple[Substitution, ...]


def unpurify_div(program: TacProgram) -> UnpurifyResult:
    """Walk every block and fold the upstream "Division purification"
    pattern back to a single ``Q = Div(A, B)`` assignment.

    Idempotent: a second run finds no patterns (the temporaries are
    gone) and is a no-op.
    """
    new_blocks: list[TacBlock] = []
    hits = 0
    subs: list[Substitution] = []
    for block in program.blocks:
        new_cmds, block_hits, block_subs = _process_block(block.commands)
        new_blocks.append(replace(block, commands=new_cmds))
        hits += block_hits
        subs.extend(block_subs)
    return UnpurifyResult(
        program=TacProgram(blocks=new_blocks),
        hits=hits,
        substitutions=tuple(subs),
    )


def _process_block(
    cmds: tuple[TacCmd, ...],
) -> tuple[list[TacCmd], int, list[Substitution]]:
    """Recognize patterns in ``cmds`` and emit the rewritten list."""
    n = len(cmds)
    hits = 0
    drops: set[int] = set()
    replacements: dict[int, TacCmd] = {}
    subs: list[Substitution] = []

    i = 0
    while i < n:
        if i in drops:
            i += 1
            continue
        match = _try_match(cmds, i)
        if match is None:
            i += 1
            continue
        q_lhs, a_expr, b_expr, indices_to_drop, replace_at_le, replace_at_havoc = match
        # The upstream Euclidean assumes are infeasible when B = 0
        # (``0 <= A`` true; ``A < 0`` false), so the original pattern
        # implicitly kills the B=0 path. ``IntDiv``'s SMT semantics
        # defines ``(div _ 0)`` (z3 returns 0), so recovering the Div
        # alone would ADD a feasible path. Make the implication
        # explicit with an upfront ``assume Gt(B, 0)`` so the rewrite
        # is sound regardless of what range analysis can prove.
        assume_b_pos = canonicalize_cmd(
            AssumeExpCmd(
                raw="",
                condition=ApplyExpr("Gt", (b_expr, _ZERO_INT)),
            )
        )
        # Q's declared sort is bv256 in practice (the havoc'd register),
        # while ``IntDiv`` returns int. Wrap with ``safe_math_narrow_bv256``
        # so the assignment's RHS sort matches Q's declared sort —
        # same shape ``R6_CEILDIV`` uses for ``IntCeilDiv``. The wrapper
        # is a no-op type assertion the encoder treats as identity.
        narrow_intdiv = ApplyExpr(
            "Apply",
            (
                SymbolRef("safe_math_narrow_bv256:bif"),
                ApplyExpr("IntDiv", (a_expr, b_expr)),
            ),
        )
        div_cmd = canonicalize_cmd(
            AssignExpCmd(
                raw="",
                lhs=q_lhs,
                rhs=narrow_intdiv,
            )
        )
        replacements[replace_at_havoc] = assume_b_pos
        replacements[replace_at_le] = div_cmd
        drops.update(indices_to_drop)
        # Trail substitution: at the original's ``Q = havoc``,
        # ``ctac run --model`` evaluates this expression instead of
        # falling back to the unconstrained sentinel. The rewriter
        # may further DCE ``Q`` from the rewritten program (if its
        # only uses go away), which is exactly the case where the
        # SMT model has no value for ``Q`` and the trail is needed.
        subs.append(
            Substitution(
                var=q_lhs,
                replacement=narrow_intdiv,
                rule="UnpurifyDiv",
            )
        )
        hits += 1
        i = max(indices_to_drop) + 1

    out: list[TacCmd] = []
    for idx, cmd in enumerate(cmds):
        if idx in drops:
            continue
        if idx in replacements:
            out.append(replacements[idx])
            continue
        out.append(cmd)
    return out, hits, subs


# ----- pattern matcher -----


def _try_match(
    cmds: tuple[TacCmd, ...], i: int
) -> tuple[str, TacExpr, TacExpr, list[int], int, int] | None:
    """If ``cmds[i:]`` starts with the purification pattern, return
    ``(Q, A_term, B, drops, replace_at_le, replace_at_havoc)``.

    - ``Q`` is the havoc'd variable name.
    - ``A_term`` is the expression on the right of ``Le`` (may be a
      ``SymbolRef`` to a kept intermediate binding).
    - ``B`` is the multiplier expression.
    - ``drops`` are the cmd indices to remove (6 indices: the two
      ``IntMul`` cmds, both ``AssumeCmd`` lines, the ``IntAdd``, and
      the ``Gt``).
    - ``replace_at_le`` is the index where the new
      ``Q = narrow(IntDiv(A_term, B))`` lands — the slot the ``Le``
      cmd held, so any intermediate ``A``-binding chain dominates
      the new use of ``A_term``.
    - ``replace_at_havoc`` is the index where the new
      ``assume Gt(B, 0)`` lands — the slot the original havoc cmd
      held. The guard makes the upstream's implicit
      "B=0 ⇒ infeasible" semantics explicit so the recovered
      ``IntDiv`` (which would otherwise be defined at B=0) is sound.
    """
    n = len(cmds)
    if i >= n:
        return None
    havoc = cmds[i]
    if not isinstance(havoc, AssignHavocCmd):
        return None
    q_lhs = havoc.lhs

    # Cmd i+1: P1 = IntMul(Q, B).
    if i + 1 >= n:
        return None
    p1 = _intmul_with_first(cmds[i + 1], q_lhs)
    if p1 is None:
        return None
    p1_lhs, b_expr = p1
    if not p1_lhs.startswith(_TMP_PREFIX):
        return None

    # Scan forward through the optional A-binding chain (each cmd is
    # an AssignExpCmd with a tacTmp!div... LHS) looking for the Le.
    le_idx: int | None = None
    a_term: TacExpr | None = None
    p3_lhs: str | None = None
    j = i + 2
    while j < n:
        c = cmds[j]
        # Try the Le first.
        le_match = _le_first_arg_is_sym(c, p1_lhs)
        if le_match is not None:
            le_idx = j
            p3_lhs, a_term = le_match
            if not p3_lhs.startswith(_TMP_PREFIX):
                return None
            break
        # Otherwise must be an A-binding intermediate.
        if not (
            isinstance(c, AssignExpCmd) and c.lhs.startswith(_TMP_PREFIX)
        ):
            return None
        j += 1
    if le_idx is None or a_term is None or p3_lhs is None:
        return None

    # assume P3
    assume_le_idx = le_idx + 1
    if assume_le_idx >= n or not _is_assume_sym(cmds[assume_le_idx], p3_lhs):
        return None
    # P4 = IntAdd(Q, 0x1)
    p4_idx = assume_le_idx + 1
    if p4_idx >= n:
        return None
    p4_lhs = _intadd_q_plus_const(cmds[p4_idx], q_lhs, 1)
    if p4_lhs is None or not p4_lhs.startswith(_TMP_PREFIX):
        return None
    # P5 = IntMul(P4, B)
    p5_idx = p4_idx + 1
    if p5_idx >= n:
        return None
    p5_lhs = _intmul_args(cmds[p5_idx], p4_lhs, b_expr)
    if p5_lhs is None or not p5_lhs.startswith(_TMP_PREFIX):
        return None
    # Optional A2-binding chain (upstream re-computes A for the Gt
    # side independently), followed by Gt(P5, A2_term).
    gt_idx: int | None = None
    p6_lhs: str | None = None
    j = p5_idx + 1
    while j < n:
        c = cmds[j]
        gt_match = _gt_first_arg_is_sym(c, p5_lhs)
        if gt_match is not None:
            gt_idx = j
            p6_lhs = gt_match[0]
            if not p6_lhs.startswith(_TMP_PREFIX):
                return None
            break
        if not (
            isinstance(c, AssignExpCmd) and c.lhs.startswith(_TMP_PREFIX)
        ):
            return None
        j += 1
    if gt_idx is None or p6_lhs is None:
        return None
    # assume P6
    assume_gt_idx = gt_idx + 1
    if assume_gt_idx >= n or not _is_assume_sym(cmds[assume_gt_idx], p6_lhs):
        return None

    drops = [
        # ``i`` (havoc) is NOT a drop — we put the `assume Gt(B, 0)`
        # there. ``le_idx`` is also not a drop — we put `Q = narrow(
        # IntDiv(A, B))` there.
        i + 1,         # P1 = IntMul(Q, B)
        assume_le_idx, # assume P3
        p4_idx,        # P4 = IntAdd(Q, 0x1)
        p5_idx,        # P5 = IntMul(P4, B)
        gt_idx,        # P6 = Gt(P5, A2_term)
        assume_gt_idx, # assume P6
    ]
    return q_lhs, a_term, b_expr, drops, le_idx, i


# ----- shape predicates -----


def _intmul_with_first(cmd: TacCmd, first_sym: str) -> tuple[str, TacExpr] | None:
    """If ``cmd`` is ``AssignExpCmd Y IntMul(SymbolRef(first_sym), other)``
    return ``(Y, other)``; the swapped arg order is also accepted."""
    if not isinstance(cmd, AssignExpCmd):
        return None
    rhs = cmd.rhs
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "IntMul" and len(rhs.args) == 2):
        return None
    a, b = rhs.args
    if isinstance(a, SymbolRef) and a.name == first_sym:
        return cmd.lhs, b
    if isinstance(b, SymbolRef) and b.name == first_sym:
        return cmd.lhs, a
    return None


def _intmul_args(cmd: TacCmd, sym: str, other: TacExpr) -> str | None:
    """If ``cmd`` is ``AssignExpCmd Y IntMul(SymbolRef(sym), other)``
    (or the swapped order) return ``Y``."""
    if not isinstance(cmd, AssignExpCmd):
        return None
    rhs = cmd.rhs
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "IntMul" and len(rhs.args) == 2):
        return None
    a, b = rhs.args
    if isinstance(a, SymbolRef) and a.name == sym and b == other:
        return cmd.lhs
    if isinstance(b, SymbolRef) and b.name == sym and a == other:
        return cmd.lhs
    return None


def _intadd_q_plus_const(cmd: TacCmd, q_sym: str, k: int) -> str | None:
    """If ``cmd`` is ``AssignExpCmd Y IntAdd(SymbolRef(q_sym), <k>)``
    (or swapped) return ``Y``."""
    if not isinstance(cmd, AssignExpCmd):
        return None
    rhs = cmd.rhs
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "IntAdd" and len(rhs.args) == 2):
        return None
    a, b = rhs.args
    if isinstance(a, SymbolRef) and a.name == q_sym and _is_int_const(b, k):
        return cmd.lhs
    if isinstance(b, SymbolRef) and b.name == q_sym and _is_int_const(a, k):
        return cmd.lhs
    return None


def _is_int_const(expr: TacExpr, value: int) -> bool:
    if not isinstance(expr, ConstExpr):
        return False
    text = expr.value.replace("_", "").strip()
    paren = text.find("(")
    if paren != -1:
        text = text[:paren]
    try:
        return int(text, 0) == value
    except ValueError:
        return False


def _le_first_arg_is_sym(cmd: TacCmd, sym: str) -> tuple[str, TacExpr] | None:
    """If ``cmd`` is ``AssignExpCmd Y Le(SymbolRef(sym), other)`` return
    ``(Y, other)`` — the first operand must be exactly ``sym``."""
    if not isinstance(cmd, AssignExpCmd):
        return None
    rhs = cmd.rhs
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "Le" and len(rhs.args) == 2):
        return None
    x, y = rhs.args
    if isinstance(x, SymbolRef) and x.name == sym:
        return cmd.lhs, y
    return None


def _gt_first_arg_is_sym(cmd: TacCmd, sym: str) -> tuple[str, TacExpr] | None:
    """If ``cmd`` is ``AssignExpCmd Y Gt(SymbolRef(sym), other)`` return
    ``(Y, other)``. The right-hand operand is the A2-term — we don't
    cross-check it against the Le-side A1-term because the upstream
    tool emits an independent A2 binding chain; structural equivalence
    is downstream's responsibility."""
    if not isinstance(cmd, AssignExpCmd):
        return None
    rhs = cmd.rhs
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "Gt" and len(rhs.args) == 2):
        return None
    x, y = rhs.args
    if isinstance(x, SymbolRef) and x.name == sym:
        return cmd.lhs, y
    return None


def _is_assume_sym(cmd: TacCmd, sym: str) -> bool:
    if not isinstance(cmd, AssumeExpCmd):
        return False
    cond = cmd.condition
    return isinstance(cond, SymbolRef) and cond.name == sym


__all__ = ["UnpurifyResult", "unpurify_div"]
