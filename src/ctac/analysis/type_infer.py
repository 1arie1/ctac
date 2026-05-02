"""Sound, possibly-incomplete kind inference for TAC registers.

Lattice ``Top (= Int+Ptr) | Int | Ptr | Bot`` over canonical TAC
symbol names (DSA :n suffixes stripped). The analysis pins each
register's kind by walking the program and applying structural
constraints:

* ``Select(M, idx)`` / ``Store(M, idx, v)`` index → ``Ptr``.
* ``Mul`` / ``Div`` / ``IntMul`` / ``IntDiv`` / ``Shift*`` /
  ``BWXOr`` / ``BNot`` operand → ``Int``.
* ``Add`` / ``IntAdd`` of one ``Ptr`` and one ``Int`` operand →
  result is ``Ptr``.
* ``Add`` / ``IntAdd`` of a ``Ptr`` and a small constant (``|c| <
  2^32``) → result is ``Ptr``. ``Sub`` / ``IntSub`` analogously:
  ``Ptr - Int`` and ``Ptr - small_const`` → ``Ptr``. The threshold
  is the inter-region distance in TAC's high-nibble address layout;
  adding a constant below it cannot move a pointer past more than
  one region boundary, so the result is still a pointer-shaped
  value (kind ``Ptr``, possibly different region in v2).
* ``narrow`` (``safe_math_narrow_bvN:bif``) is identity:
  ``lhs ≡ inner``.
* ``BWAnd(R, const)`` / ``BWOr(R, const)`` is identity (alignment
  and tag-set both preserve kind).
* ``R = SymbolRef(R')`` and ``assume R == R'`` unify classes.
* ``Ite(c, t, e)`` → ``join(kind(t), kind(e))``.

The analysis abstains rather than risk unsoundness on
``Mod``/``IntMod``, comparisons, ``Sub``-asymmetric, and
two-non-constant ``BWAnd``/``BWOr``. Constants do not seed kind.

Bot indicates an unsatisfiable constraint set on a class — either
ill-typed program or an analysis precision loss; both are sound
report-out values.

Pass a ``trace_sink`` to ``analyze_types`` to receive one
``TypeTraceEntry`` per constraint event (every ``meet_kind`` /
``union`` attempt, plus per-AssignExpCmd RHS evaluation summary).
The trace is the diagnostic answer to "why is X this kind?" — if a
class ends up ``Top``, the trace shows what attempts were made and
what kinds they tried to apply; if it ends up ``Bot``, the trace
shows the two contradicting events."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Callable

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpiCmd,
    SymbolRef,
    TacExpr,
)
from ctac.ast.range_constraints import const_expr_to_int
from ctac.ir.models import TacProgram


# Conservative upper bound on the magnitude of a constant offset that we
# treat as "definitely cannot escape the pointer region(s)" when added to a
# Ptr-classified register. Region prefixes in TAC's high-nibble layout sit
# at multiples of 2^32 (`0x{01,02,03,04}00000000`), so a constant whose
# absolute value is strictly less than 2^32 can shift a pointer by at most
# one region. Each such shift lands in another pointer-shaped value (still
# kind Ptr in our v1 lattice). Practical SBF offsets — struct fields,
# array element offsets — are far below this threshold (typically <= 2^16);
# 2^32 is the soundness ceiling, not a tightness target.
_PTR_OFFSET_LIMIT = 1 << 32


class TypeKind(str, Enum):
    """Kind lattice for TAC register inference."""

    TOP = "Top"
    INT = "Int"
    PTR = "Ptr"
    BOT = "Bot"


# Hard ``Int`` operands: positions where pointer semantics is undefined.
# Mod / IntMod / comparisons are intentionally absent — pointer-mod
# (alignment-extraction) and same-region pointer comparisons are valid.
_INT_OPERAND_OPS: frozenset[str] = frozenset(
    {
        "Mul",
        "Div",
        "IntMul",
        "IntDiv",
        "ShiftLeft",
        "ShiftRightLogical",
        "ShiftRightArithmetical",
        "BWXOr",
        "BNot",
    }
)


def meet(a: TypeKind, b: TypeKind) -> TypeKind:
    """Greatest-lower-bound on the kind lattice."""
    if a == b:
        return a
    if a == TypeKind.TOP:
        return b
    if b == TypeKind.TOP:
        return a
    if a == TypeKind.BOT or b == TypeKind.BOT:
        return TypeKind.BOT
    # One is INT, the other PTR -> contradiction.
    return TypeKind.BOT


def join(a: TypeKind, b: TypeKind) -> TypeKind:
    """Least-upper-bound on the kind lattice."""
    if a == b:
        return a
    if a == TypeKind.BOT:
        return b
    if b == TypeKind.BOT:
        return a
    # One TOP, or {INT, PTR} mismatch -> TOP.
    return TypeKind.TOP


def _is_safe_math_narrow_name(name: str) -> bool:
    return name.startswith("safe_math_narrow_bv") and name.endswith(":bif")


def _is_small_const_offset(expr: TacExpr) -> bool:
    """True iff ``expr`` is a constant whose magnitude is below the
    region-distance threshold ``_PTR_OFFSET_LIMIT``. Used by the Add/Sub
    asymmetric rule to recognize ``Ptr ± small_const`` as ``Ptr``."""
    if not isinstance(expr, ConstExpr):
        return False
    n = const_expr_to_int(expr)
    if n is None:
        return False
    return abs(n) < _PTR_OFFSET_LIMIT


def _unwrap_apply(expr: ApplyExpr) -> tuple[str, tuple[TacExpr, ...]]:
    """Return (op, args) with the canonical ``Apply(SymRef, ...)`` unwrapping.

    For an ``Apply`` whose ``args[0]`` is a SymRef holding the function
    symbol name (e.g. ``safe_math_narrow_bv256:bif``), unwrap so callers
    see the function name as ``op`` directly. Mirrors the convention used
    in ``ctac.analysis.abs_int.domains.poly_deg``.
    """
    op = expr.op
    args = expr.args
    if op == "Apply" and args and isinstance(args[0], SymbolRef):
        return args[0].name, args[1:]
    return op, args


@dataclass(frozen=True)
class TypeTraceEntry:
    """One record per constraint event during kind inference.

    ``kind`` is the event kind (``meet`` for ``meet_kind`` calls; ``union``
    for ``union`` calls; ``rhs-eval`` for the per-AssignExpCmd summary that
    pairs ``lhs`` with the kind its RHS evaluated to).

    ``before`` / ``after`` are the kinds before and after applying the rule.
    For ``meet`` they are the class kind; for ``union`` they are the
    surviving class's kind (post-merge ``after`` reflects the meet of both
    sides' kinds). For ``rhs-eval`` they are the lhs's class kind before
    and after meeting with the RHS-evaluated kind.

    ``rule`` is a short tag identifying which rule fired (e.g.
    ``select-index``, ``mul-operand``, ``narrow-unify``, ``rhs-meet``).

    ``symbols`` is the canonical symbols affected (one for ``meet`` and
    ``rhs-eval``; two for ``union``).

    ``detail`` is a short human-readable context (e.g. the operator name
    and the SymRef being constrained)."""

    phase: str
    iteration: int
    block_id: str
    cmd_index: int
    kind: str  # "meet" | "union" | "rhs-eval"
    rule: str
    symbols: tuple[str, ...]
    before: str
    after: str
    detail: str
    changed: bool


TypeTraceSink = Callable[[TypeTraceEntry], None]


@dataclass
class _TraceCtx:
    """Mutable per-step trace context. Threaded through the analysis."""

    sink: TypeTraceSink | None
    phase: str = "pre-pass"
    iteration: int = 0
    block_id: str = ""
    cmd_index: int = -1


class _UnionFind:
    """Path-compressed union-find with a kind label per class root.

    Trace events fire on every ``meet_kind`` and ``union`` call (regardless
    of whether the call changed state) so a downstream consumer can see
    both events that fired and events that were no-ops — the latter is
    useful for diagnosing "why didn't this register tighten?"."""

    def __init__(self, trace_ctx: _TraceCtx) -> None:
        self._parent: dict[str, str] = {}
        self._rank: dict[str, int] = {}
        self._kind: dict[str, TypeKind] = {}
        self._trace = trace_ctx

    def make(self, name: str) -> None:
        if name not in self._parent:
            self._parent[name] = name
            self._rank[name] = 0
            self._kind[name] = TypeKind.TOP

    def find(self, name: str) -> str:
        self.make(name)
        # Two-pass path compression.
        root = name
        while self._parent[root] != root:
            root = self._parent[root]
        cur = name
        while self._parent[cur] != root:
            self._parent[cur], cur = root, self._parent[cur]
        return root

    def union(self, a: str, b: str, *, rule: str, detail: str) -> bool:
        ra, rb = self.find(a), self.find(b)
        before_a = self._kind[ra]
        before_b = self._kind[rb]
        if ra == rb:
            self._emit(
                event_kind="union",
                rule=rule,
                symbols=(a, b),
                before=before_a.value,
                after=before_a.value,
                detail=detail,
                changed=False,
            )
            return False
        if self._rank[ra] < self._rank[rb]:
            ra, rb = rb, ra
            before_a, before_b = before_b, before_a
        merged = meet(before_a, before_b)
        self._parent[rb] = ra
        if self._rank[ra] == self._rank[rb]:
            self._rank[ra] += 1
        self._kind[ra] = merged
        del self._kind[rb]
        # The "before" we report is the surviving root's pre-merge kind;
        # consumers can read both ``before`` and ``after`` to see the
        # meet outcome.
        self._emit(
            event_kind="union",
            rule=rule,
            symbols=(a, b),
            before=before_a.value,
            after=merged.value,
            detail=detail,
            changed=True,
        )
        return True

    def get_kind(self, name: str) -> TypeKind:
        return self._kind[self.find(name)]

    def meet_kind(self, name: str, k: TypeKind, *, rule: str, detail: str) -> bool:
        r = self.find(name)
        old = self._kind[r]
        new = meet(old, k)
        changed = new != old
        self._emit(
            event_kind="meet",
            rule=rule,
            symbols=(name,),
            before=old.value,
            after=new.value,
            detail=f"{detail} (attempted={k.value})",
            changed=changed,
        )
        if changed:
            self._kind[r] = new
        return changed

    def all_names(self) -> list[str]:
        return list(self._parent)

    def _emit(
        self,
        *,
        event_kind: str,
        rule: str,
        symbols: tuple[str, ...],
        before: str,
        after: str,
        detail: str,
        changed: bool,
    ) -> None:
        sink = self._trace.sink
        if sink is None:
            return
        sink(
            TypeTraceEntry(
                phase=self._trace.phase,
                iteration=self._trace.iteration,
                block_id=self._trace.block_id,
                cmd_index=self._trace.cmd_index,
                kind=event_kind,
                rule=rule,
                symbols=symbols,
                before=before,
                after=after,
                detail=detail,
                changed=changed,
            )
        )


@dataclass
class TypeInferResult:
    """Per-canonical-symbol kind table plus class-membership view."""

    kind: dict[str, TypeKind] = field(default_factory=dict)
    """canonical symbol name → final kind"""

    class_id: dict[str, str] = field(default_factory=dict)
    """canonical symbol name → class root (representative name)"""

    class_members: dict[str, list[str]] = field(default_factory=dict)
    """class root → sorted member names"""

    iterations: int = 0
    """Number of fixpoint iterations executed (excluding the pre-pass)."""

    def kinds_by(self, k: TypeKind) -> list[str]:
        return sorted(name for name, kk in self.kind.items() if kk == k)


def _collect_equalities_and_register(
    uf: _UnionFind, program: TacProgram, trace_ctx: _TraceCtx
) -> None:
    """First sweep: register every TAC symbol and apply structural unions
    that don't depend on resolved kinds (assignment-as-copy, narrow-of-symref,
    BWAnd/BWOr-with-const passthrough, ``assume R == R'``)."""

    def _register_symbols(expr: TacExpr) -> None:
        if isinstance(expr, SymbolRef):
            uf.make(canonical_symbol(expr.name))
        elif isinstance(expr, ApplyExpr):
            for a in expr.args:
                _register_symbols(a)

    def _maybe_union_passthrough(lhs: str, rhs: TacExpr) -> None:
        # R = SymRef(R')  -> unify
        if isinstance(rhs, SymbolRef):
            other = canonical_symbol(rhs.name)
            uf.union(
                lhs,
                other,
                rule="copy-assign",
                detail=f"{lhs} = {other}",
            )
            return
        if not isinstance(rhs, ApplyExpr):
            return
        op, args = _unwrap_apply(rhs)
        # R = narrow(SymRef)  -> unify
        if _is_safe_math_narrow_name(op) and len(args) == 1 and isinstance(
            args[0], SymbolRef
        ):
            other = canonical_symbol(args[0].name)
            uf.union(
                lhs, other, rule="narrow-unify", detail=f"{lhs} = narrow({other})"
            )
            return
        # R = BWAnd/BWOr(SymRef, const) | (const, SymRef)  -> unify
        if op in ("BWAnd", "BWOr") and len(args) == 2:
            a, b = args[0], args[1]
            if isinstance(a, SymbolRef) and isinstance(b, ConstExpr):
                uf.union(
                    lhs,
                    canonical_symbol(a.name),
                    rule=f"{op.lower()}-passthrough",
                    detail=f"{lhs} = {op}({a.name}, {b.value})",
                )
            elif isinstance(b, SymbolRef) and isinstance(a, ConstExpr):
                uf.union(
                    lhs,
                    canonical_symbol(b.name),
                    rule=f"{op.lower()}-passthrough",
                    detail=f"{lhs} = {op}({a.value}, {b.name})",
                )

    def _maybe_union_from_assume(cond: TacExpr) -> None:
        if not isinstance(cond, ApplyExpr):
            return
        op, args = _unwrap_apply(cond)
        # ``assume R == R'`` (Eq with two SymRefs) -> unify. ``assume R ==
        # const`` would attempt to seed kind from a constant — skipped, see
        # the design note in the module docstring.
        if op == "Eq" and len(args) == 2:
            a, b = args[0], args[1]
            if isinstance(a, SymbolRef) and isinstance(b, SymbolRef):
                uf.union(
                    canonical_symbol(a.name),
                    canonical_symbol(b.name),
                    rule="assume-equality",
                    detail=f"assume {a.name} == {b.name}",
                )

    trace_ctx.phase = "pre-pass"
    trace_ctx.iteration = 0
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            trace_ctx.block_id = block.id
            trace_ctx.cmd_index = idx
            if isinstance(cmd, AssignExpCmd):
                lhs = canonical_symbol(cmd.lhs)
                uf.make(lhs)
                _register_symbols(cmd.rhs)
                _maybe_union_passthrough(lhs, cmd.rhs)
            elif isinstance(cmd, AssumeExpCmd):
                _register_symbols(cmd.condition)
                _maybe_union_from_assume(cmd.condition)
            elif isinstance(cmd, AssignHavocCmd):
                uf.make(canonical_symbol(cmd.lhs))
            elif isinstance(cmd, JumpiCmd):
                uf.make(canonical_symbol(cmd.condition))
            elif isinstance(cmd, AssertCmd):
                _register_symbols(cmd.predicate)


def _walk_and_apply(uf: _UnionFind, expr: TacExpr) -> tuple[TypeKind, bool]:
    """Walk an expression bottom-up. At each operator position emit any
    hard kind constraints on operands, then return the kind the expression
    itself reduces to. Returns ``(kind, changed)``.

    Sound-by-construction: every constraint corresponds to a position
    whose kind is dictated by the surrounding operator's semantics."""

    if isinstance(expr, ConstExpr):
        return TypeKind.TOP, False
    if isinstance(expr, SymbolRef):
        return uf.get_kind(canonical_symbol(expr.name)), False
    if not isinstance(expr, ApplyExpr):
        return TypeKind.TOP, False

    op, args = _unwrap_apply(expr)
    changed = False
    arg_kinds: list[TypeKind] = []
    for a in args:
        k, c = _walk_and_apply(uf, a)
        if c:
            changed = True
        arg_kinds.append(k)

    # ---- hard PTR meets: index of memory ops ----
    if op in ("Select", "Store") and len(args) >= 2:
        idx = args[1]
        if isinstance(idx, SymbolRef):
            rule = "select-index" if op == "Select" else "store-index"
            if uf.meet_kind(
                canonical_symbol(idx.name),
                TypeKind.PTR,
                rule=rule,
                detail=f"{op}(_, {idx.name})",
            ):
                changed = True

    # ---- hard INT meets: arithmetic operands ----
    if op in _INT_OPERAND_OPS:
        for ai, a in enumerate(args):
            if isinstance(a, SymbolRef):
                if uf.meet_kind(
                    canonical_symbol(a.name),
                    TypeKind.INT,
                    rule=f"{op.lower()}-operand",
                    detail=f"{op}(... arg{ai}={a.name} ...)",
                ):
                    changed = True

    # ---- determine kind of the expression itself ----
    result_kind: TypeKind
    if _is_safe_math_narrow_name(op) and len(args) == 1:
        # Identity in SMT — kind passthrough.
        result_kind = arg_kinds[0]
    elif op in ("Add", "IntAdd") and len(args) == 2:
        a, b = args[0], args[1]
        ka, kb = arg_kinds[0], arg_kinds[1]
        if ka == TypeKind.BOT or kb == TypeKind.BOT:
            result_kind = TypeKind.BOT
        elif (ka == TypeKind.PTR and kb == TypeKind.INT) or (
            ka == TypeKind.INT and kb == TypeKind.PTR
        ):
            result_kind = TypeKind.PTR
        elif ka == TypeKind.PTR and _is_small_const_offset(b):
            # Ptr + small_const — pointer arithmetic by a constant
            # offset stays within at most one region boundary.
            result_kind = TypeKind.PTR
        elif kb == TypeKind.PTR and _is_small_const_offset(a):
            result_kind = TypeKind.PTR
        else:
            # Int+Int, any Top operand without a small-const partner,
            # or Ptr+Ptr — abstain. Ptr+Ptr could be flagged Bot but
            # we leave it Top for v1 (sound, imprecise).
            result_kind = TypeKind.TOP
    elif op in ("Sub", "IntSub") and len(args) == 2:
        # Sub is asymmetric in argument order: only the LHS may be Ptr.
        # ``Sub(Int, Ptr)`` and ``Sub(small_const, Ptr)`` are not
        # pointer-shaped values in any sensible semantics; abstain there.
        # ``Sub(Ptr, Ptr) = Int`` (pointer difference) is deferred to v2.
        a, b = args[0], args[1]
        ka, kb = arg_kinds[0], arg_kinds[1]
        if ka == TypeKind.BOT or kb == TypeKind.BOT:
            result_kind = TypeKind.BOT
        elif ka == TypeKind.PTR and kb == TypeKind.INT:
            result_kind = TypeKind.PTR
        elif ka == TypeKind.PTR and _is_small_const_offset(b):
            result_kind = TypeKind.PTR
        else:
            result_kind = TypeKind.TOP
    elif op == "Ite" and len(args) == 3:
        result_kind = join(arg_kinds[1], arg_kinds[2])
    elif op in ("BWAnd", "BWOr") and len(args) == 2:
        a, b = args[0], args[1]
        if isinstance(a, ConstExpr) and not isinstance(b, ConstExpr):
            result_kind = arg_kinds[1]
        elif isinstance(b, ConstExpr) and not isinstance(a, ConstExpr):
            result_kind = arg_kinds[0]
        else:
            result_kind = TypeKind.TOP
    elif op in _INT_OPERAND_OPS:
        # Arithmetic result is itself an Int.
        result_kind = TypeKind.INT
    else:
        # Select-loaded values, comparisons, Bool ops, Apply-of-other-bif,
        # IntMod, Mod, Sub, IntSub, Eq/Ne, etc. — abstain.
        result_kind = TypeKind.TOP

    return result_kind, changed


def _expr_summary(expr: TacExpr) -> str:
    """Very-short one-line summary of an expression for trace context.
    Renders Apply as the function name, ApplyExpr as ``op(arg-summaries)``
    truncated to depth 2 to keep records readable."""

    def go(e: TacExpr, depth: int) -> str:
        if isinstance(e, ConstExpr):
            return e.value
        if isinstance(e, SymbolRef):
            return e.name
        if isinstance(e, ApplyExpr):
            op, args = _unwrap_apply(e)
            if depth <= 0:
                return f"{op}(...)"
            inner = ", ".join(go(a, depth - 1) for a in args)
            return f"{op}({inner})"
        return "?"

    return go(expr, 2)


def _process_command(uf: _UnionFind, cmd, trace_ctx: _TraceCtx) -> bool:
    changed = False
    if isinstance(cmd, AssignExpCmd):
        rhs_kind, c = _walk_and_apply(uf, cmd.rhs)
        if c:
            changed = True
        lhs = canonical_symbol(cmd.lhs)
        # Synthesize a per-AssignExpCmd RHS-eval record so the user can
        # see what the analysis concluded the RHS resolves to. Independent
        # of whether the meet actually changes the lhs class — even a
        # no-change meet is informative ("RHS evaluated to TOP, so lhs
        # stays at its current kind").
        if trace_ctx.sink is not None:
            current = uf.get_kind(lhs)
            trace_ctx.sink(
                TypeTraceEntry(
                    phase=trace_ctx.phase,
                    iteration=trace_ctx.iteration,
                    block_id=trace_ctx.block_id,
                    cmd_index=trace_ctx.cmd_index,
                    kind="rhs-eval",
                    rule="rhs-meet",
                    symbols=(lhs,),
                    before=current.value,
                    after=meet(current, rhs_kind).value,
                    detail=f"{lhs} = {_expr_summary(cmd.rhs)} -> rhs_kind={rhs_kind.value}",
                    changed=meet(current, rhs_kind) != current,
                )
            )
        if uf.meet_kind(
            lhs,
            rhs_kind,
            rule="rhs-meet",
            detail=f"lhs = {_expr_summary(cmd.rhs)}",
        ):
            changed = True
    elif isinstance(cmd, AssumeExpCmd):
        _, c = _walk_and_apply(uf, cmd.condition)
        if c:
            changed = True
    elif isinstance(cmd, AssertCmd):
        _, c = _walk_and_apply(uf, cmd.predicate)
        if c:
            changed = True
    return changed


def analyze_types(
    program: TacProgram, *, trace_sink: TypeTraceSink | None = None
) -> TypeInferResult:
    """Run kind inference over ``program`` to a fixed point.

    The result reports per-canonical-symbol kind plus class membership,
    which is useful for spotting registers that share an equivalence
    class via copy / narrow / alignment passthrough.

    Pass ``trace_sink`` to receive one ``TypeTraceEntry`` per constraint
    event (every meet, every union, plus a per-AssignExpCmd RHS-eval
    summary). The sink is invoked synchronously during analysis."""

    trace_ctx = _TraceCtx(sink=trace_sink)
    uf = _UnionFind(trace_ctx)
    _collect_equalities_and_register(uf, program, trace_ctx)

    iterations = 0
    while True:
        iterations += 1
        trace_ctx.phase = "fixpoint"
        trace_ctx.iteration = iterations
        any_change = False
        for block in program.blocks:
            for idx, cmd in enumerate(block.commands):
                trace_ctx.block_id = block.id
                trace_ctx.cmd_index = idx
                if _process_command(uf, cmd, trace_ctx):
                    any_change = True
        if not any_change:
            break

    # Materialize results. Every name in the union-find is queried for
    # its canonical class kind, and class members are grouped by root.
    kind: dict[str, TypeKind] = {}
    class_id: dict[str, str] = {}
    members_by_root: dict[str, list[str]] = {}
    for name in uf.all_names():
        root = uf.find(name)
        k = uf.get_kind(name)
        kind[name] = k
        class_id[name] = root
        members_by_root.setdefault(root, []).append(name)
    for root in members_by_root:
        members_by_root[root].sort()

    return TypeInferResult(
        kind=kind,
        class_id=class_id,
        class_members=members_by_root,
        iterations=iterations,
    )
