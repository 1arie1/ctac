"""Hoist defs that are semantically path-invariant under the branch
condition.

When a join's dynamic-defed symbol ``X`` has two defs that compute the
same value under their respective branch conditions (one branch in a
"simple" const-folded form, the other in the un-folded complex form),
we can compute the complex form ONCE before the branch and replace both
branch defs with an alias.

Two recognized patterns (initial inventory):

(1) **muldiv-equal-divisor.** Under ``cond = Eq(p, q)`` with ``q > 0``,
    ``muldiv(a, p, q) == a``. The complex branch has a
    ``muldiv(a, b, c)`` chain (possibly wrapped in ``narrow``); the
    simple branch has ``a`` directly.

(2) **narrow-zero-mul.** Under ``cond = Eq(x, 0)``,
    ``narrow(K * x) == 0`` for any const ``K``. The complex branch has
    ``narrow(IntMul(K, x))`` (or ``IntMul(K, x)``); the simple branch
    has ``0``.

For each match, emit a fresh ``HV<N> = <complex_rhs>`` (plus any
ancillary inner defs) at the end of the JumpiCmd's host block — right
before the JumpiCmd terminator — and rewrite both branch assignments
of X to ``X = HV<N>``.

Soundness:

- The hoisted def's operands are all defined at the JumpiCmd's host
  block (or earlier); they reach the new position by dominance.
- The complex form is the actual value the original program computed
  on the complex branch — equality there is structural.
- On the simple branch, equality holds under the branch condition via
  the recognizer's identity (muldiv axiom + ``q > 0`` for #1;
  ``K * 0 = 0`` and ``narrow(0) = 0`` for #2). rw-eq's rule-2 CHK
  ``Eq(simple_rhs, HV<N>)`` discharges under the branch's BLK guard.

The original chain in the complex branch becomes dead via DCE once X's
def references the hoisted alias instead. Any range-assume on the
chain (e.g. ``assume I171 in [0, 2^64-1]``) stays in its original
branch — hoisting the assume is a separate optimization gated on its
content being derivable from in-scope facts at the target (which is
not generally true for the muldiv u64 cap).
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssignExpCmd,
    ConstExpr,
    JumpiCmd,
    LabelCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import MUL_OPS, const_to_int
from ctac.rewrite.unparse import canonicalize_cmd


@dataclass(frozen=True)
class HoistPathInvariantResult:
    program: TacProgram
    hits: int = 0
    fresh_symbols: tuple[tuple[str, str], ...] = ()


def _peel_narrow(expr: TacExpr) -> TacExpr:
    if _is_safe_narrow_apply(expr):
        assert isinstance(expr, ApplyExpr)
        return expr.args[1]
    return expr


def _is_const(expr: TacExpr, value: int) -> bool:
    return isinstance(expr, ConstExpr) and const_to_int(expr) == value


def _canonical(expr: TacExpr) -> TacExpr:
    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical(a) for a in expr.args))
    return expr


def _eq_modulo_meta(a: TacExpr, b: TacExpr) -> bool:
    return _canonical(a) == _canonical(b)


def _match_eq_cond(cond_def: TacExpr) -> tuple[TacExpr, TacExpr] | None:
    """``Eq(p, q)`` → ``(p, q)`` (caller handles arg-order in patterns)."""
    if not (
        isinstance(cond_def, ApplyExpr)
        and cond_def.op == "Eq"
        and len(cond_def.args) == 2
    ):
        return None
    return cond_def.args


def _resolve_complex_chain(rhs: TacExpr, ctx: RewriteCtx) -> TacExpr:
    """Chase one SymRef + one narrow wrapper to reach the next
    ApplyExpr. Stops as soon as the chase reaches a non-SymRef
    non-Apply form, so we don't dive into the operand layer."""
    seen: set[str] = set()
    cur = rhs
    while True:
        if isinstance(cur, SymbolRef):
            canon = canonical_symbol(cur.name)
            if canon in seen:
                return cur
            seen.add(canon)
            d = ctx.definition(cur.name)
            if d is None:
                return cur
            cur = d
            continue
        if _is_safe_narrow_apply(cur):
            assert isinstance(cur, ApplyExpr)
            cur = cur.args[1]
            continue
        return cur


def _recognize_muldiv_equal_divisor(
    simple_rhs: TacExpr,
    complex_chain: TacExpr,
    cond_args: tuple[TacExpr, TacExpr],
    ctx: RewriteCtx,
) -> TacExpr | None:
    """muldiv-equal-divisor pattern.

    Returns the complex RHS to hoist (typically ``muldiv(a, b, c)`` or
    a narrow-wrapped form) when the recognizer matches; otherwise None.
    """
    if not (
        isinstance(complex_chain, ApplyExpr)
        and complex_chain.op == "IntMulDiv"
        and len(complex_chain.args) == 3
    ):
        return None
    a, b, c = complex_chain.args
    # simple_rhs must equal `a`.
    if not _eq_modulo_meta(simple_rhs, a):
        return None
    # Cond's (p, q) must match (b, c) in some order.
    p, q = cond_args
    matches_order = _eq_modulo_meta(b, p) and _eq_modulo_meta(c, q)
    matches_swap = _eq_modulo_meta(b, q) and _eq_modulo_meta(c, p)
    if not (matches_order or matches_swap):
        return None
    # Divisor must be positive (so muldiv axiom applies).
    c_range = infer_expr_range(c, ctx)
    if c_range is None or c_range[0] is None or c_range[0] < 1:
        return None
    return complex_chain


def _recognize_narrow_zero_mul(
    simple_rhs: TacExpr,
    complex_chain: TacExpr,
    cond_args: tuple[TacExpr, TacExpr],
) -> TacExpr | None:
    """narrow-zero-mul pattern. Returns the complex RHS to hoist."""
    if not _is_const(simple_rhs, 0):
        return None
    # complex_chain itself may be the IntMul, or a narrow-wrapped form.
    inner = _peel_narrow(complex_chain)
    if not (
        isinstance(inner, ApplyExpr)
        and inner.op in MUL_OPS
        and len(inner.args) == 2
    ):
        return None
    # One arg must be a constant K; the other must match cond's "x"
    # operand (the side where cond is `Eq(x, 0)`).
    p, q = cond_args
    if _is_const(p, 0):
        x = q
    elif _is_const(q, 0):
        x = p
    else:
        return None
    m_l, m_r = inner.args
    if isinstance(m_l, ConstExpr) and _eq_modulo_meta(m_r, x):
        pass
    elif isinstance(m_r, ConstExpr) and _eq_modulo_meta(m_l, x):
        pass
    else:
        return None
    return complex_chain


def _terminator_index(block: TacBlock) -> int | None:
    if not block.commands:
        return None
    last = block.commands[-1]
    if not isinstance(last, JumpiCmd):
        return None
    return len(block.commands) - 1


def _last_insertable_idx(block: TacBlock, jumpi_idx: int) -> int | None:
    """The cmd index after which the hoisted def can be safely inserted.
    Walk back past trailing AnnotationCmd / LabelCmd attached to the
    JumpiCmd; return the index of the first earlier real cmd.

    Returns None when the block has nothing but the terminator (rare;
    skip the hoist in that case).
    """
    skip = (AnnotationCmd, LabelCmd)
    j = jumpi_idx - 1
    while j >= 0 and isinstance(block.commands[j], skip):
        j -= 1
    if j < 0:
        return None
    return j


@dataclass(frozen=True)
class _HoistAction:
    host_block: str
    insert_after_idx: int
    # New cmds to insert after `insert_after_idx`.
    new_cmds: tuple[TacCmd, ...]
    # Replacements for the two branch defs of the dynamic symbol.
    replacements: tuple[tuple[str, int, TacCmd], ...]
    # Fresh symbol declarations introduced by the hoist.
    fresh_symbols: tuple[tuple[str, str], ...]


def hoist_path_invariant_defs(
    program: TacProgram,
    *,
    symbol_sorts: "dict[str, str] | None" = None,
) -> HoistPathInvariantResult:
    """Walk JumpiCmds; hoist semantically-equivalent branch defs."""
    sorts = symbol_sorts or {}
    ctx = RewriteCtx(program, symbol_sorts=sorts)
    by_id = program.block_by_id()

    # Dynamic-symbol → list[(block_id, cmd_index)] of its defs.
    sym_defs: dict[str, list[tuple[str, int]]] = {}
    for assn in ctx.dsa.dynamic_assignments:
        sym_defs.setdefault(
            canonical_symbol(assn.symbol), []
        ).append((assn.block_id, assn.cmd_index))

    actions: list[_HoistAction] = []
    fresh_counter = 0
    reserved: set[str] = set(sorts.keys())

    def _alloc_fresh(prefix: str = "HV") -> str:
        nonlocal fresh_counter
        while True:
            name = f"{prefix}{fresh_counter}"
            fresh_counter += 1
            if name in reserved:
                continue
            reserved.add(name)
            return name

    for block in program.blocks:
        jumpi_idx = _terminator_index(block)
        if jumpi_idx is None:
            continue
        terminator = block.commands[jumpi_idx]
        assert isinstance(terminator, JumpiCmd)
        cond_def = ctx.definition(terminator.condition)
        if cond_def is None:
            continue
        eq_args = _match_eq_cond(cond_def)
        if eq_args is None:
            continue
        t_block_id, e_block_id = (
            terminator.then_target,
            terminator.else_target,
        )
        if t_block_id not in by_id or e_block_id not in by_id:
            continue
        insert_after = _last_insertable_idx(block, jumpi_idx)
        if insert_after is None:
            continue

        for sym, sites in sym_defs.items():
            t_sites = [(b, i) for (b, i) in sites if b == t_block_id]
            e_sites = [(b, i) for (b, i) in sites if b == e_block_id]
            if len(t_sites) != 1 or len(e_sites) != 1:
                continue
            (_, t_idx), (_, e_idx) = t_sites[0], e_sites[0]
            t_cmd = by_id[t_block_id].commands[t_idx]
            e_cmd = by_id[e_block_id].commands[e_idx]
            if not (
                isinstance(t_cmd, AssignExpCmd)
                and isinstance(e_cmd, AssignExpCmd)
            ):
                continue

            # Try simple = t-arm, complex = e-arm.
            simple_cmd, complex_cmd = t_cmd, e_cmd
            simple_block, simple_idx_l = t_block_id, t_idx
            complex_block, complex_idx_l = e_block_id, e_idx
            complex_chain = _resolve_complex_chain(complex_cmd.rhs, ctx)
            hoisted_rhs = _try_recognize(
                simple_cmd.rhs, complex_chain, eq_args, ctx
            )
            if hoisted_rhs is None:
                # Swap and try the other arm as simple.
                simple_cmd, complex_cmd = e_cmd, t_cmd
                simple_block, simple_idx_l = e_block_id, e_idx
                complex_block, complex_idx_l = t_block_id, t_idx
                complex_chain = _resolve_complex_chain(complex_cmd.rhs, ctx)
                hoisted_rhs = _try_recognize(
                    simple_cmd.rhs, complex_chain, eq_args, ctx
                )
                if hoisted_rhs is None:
                    continue

            # Emit hoisted def + rewrite both branches. `raw` must be
            # regenerated via canonicalize_cmd; the renderer prefers
            # the raw field over the structured fields, so a stale raw
            # would silently keep the original RHS in the output.
            lhs_name = _alloc_fresh()
            sort = sorts.get(canonical_symbol(sym), "bv256")
            hoisted_def = canonicalize_cmd(
                AssignExpCmd(raw="", lhs=lhs_name, rhs=hoisted_rhs)
            )
            new_simple_cmd = canonicalize_cmd(
                replace(simple_cmd, raw="", rhs=SymbolRef(lhs_name))
            )
            new_complex_cmd = canonicalize_cmd(
                replace(complex_cmd, raw="", rhs=SymbolRef(lhs_name))
            )
            actions.append(
                _HoistAction(
                    host_block=block.id,
                    insert_after_idx=insert_after,
                    new_cmds=(hoisted_def,),
                    replacements=(
                        (simple_block, simple_idx_l, new_simple_cmd),
                        (complex_block, complex_idx_l, new_complex_cmd),
                    ),
                    fresh_symbols=((lhs_name, sort),),
                )
            )

    if not actions:
        return HoistPathInvariantResult(
            program=program, hits=0, fresh_symbols=()
        )

    insertions: dict[tuple[str, int], list[TacCmd]] = {}
    replacements: dict[tuple[str, int], TacCmd] = {}
    all_fresh: list[tuple[str, str]] = []
    for action in actions:
        insertions.setdefault(
            (action.host_block, action.insert_after_idx), []
        ).extend(action.new_cmds)
        for (b, i, new_cmd) in action.replacements:
            replacements[(b, i)] = new_cmd
        all_fresh.extend(action.fresh_symbols)

    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            new_cmds.append(replacements.get((block.id, idx), cmd))
            for q in insertions.get((block.id, idx), ()):
                new_cmds.append(q)
        new_blocks.append(replace(block, commands=new_cmds))

    return HoistPathInvariantResult(
        program=TacProgram(blocks=new_blocks),
        hits=len(actions),
        fresh_symbols=tuple(all_fresh),
    )


def _try_recognize(
    simple_rhs: TacExpr,
    complex_chain: TacExpr,
    cond_args: tuple[TacExpr, TacExpr],
    ctx: RewriteCtx,
) -> TacExpr | None:
    """Try each recognizer in turn; return the hoisted-rhs on first match."""
    result = _recognize_muldiv_equal_divisor(
        simple_rhs, complex_chain, cond_args, ctx
    )
    if result is not None:
        return result
    return _recognize_narrow_zero_mul(simple_rhs, complex_chain, cond_args)


__all__ = ["HoistPathInvariantResult", "hoist_path_invariant_defs"]
