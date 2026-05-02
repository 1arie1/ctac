"""Kind-inference (`ctac types`) analysis tests.

Each test pins one of the structural rules from the design doc:

    Select/Store index            -> Ptr meet
    Mul/Div/IntMul/IntDiv operand -> Int meet
    narrow / BWAnd-const          -> passthrough (unification)
    R = SymRef(R')                -> unification
    assume R == R'                -> unification
    Add(Ptr, Int) | (Int, Ptr)    -> result Ptr
    Mul-then-Select on same class -> Bot
    Ite-of-two-symrefs            -> join

Soundness: the analysis must never label a register `Int` if it is
used as a `Select`/`Store` index, and never label `Ptr` if it is used
as an operand of arithmetic ops where pointers are nonsensical.
"""

from __future__ import annotations

from ctac.analysis.type_infer import TypeKind, analyze_types
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram


def _block(bid: str, succs: list[str], cmds: list[TacCmd]) -> TacBlock:
    return TacBlock(id=bid, successors=succs, commands=cmds)


def _assign(lhs: str, rhs: TacExpr) -> AssignExpCmd:
    return AssignExpCmd(raw=f"{lhs} = ...", lhs=lhs, rhs=rhs)


def _havoc(lhs: str) -> AssignHavocCmd:
    return AssignHavocCmd(raw=f"{lhs} = havoc", lhs=lhs)


def _assume(cond: TacExpr) -> AssumeExpCmd:
    return AssumeExpCmd(raw="AssumeExpCmd ...", condition=cond)


def _sym(name: str) -> SymbolRef:
    return SymbolRef(name=name)


def _const(v: str) -> ConstExpr:
    return ConstExpr(value=v)


def _apply(op: str, *args: TacExpr) -> ApplyExpr:
    return ApplyExpr(op=op, args=tuple(args))


def _narrow(arg: TacExpr) -> ApplyExpr:
    """`Apply(safe_math_narrow_bv256:bif, arg)` — the canonical form
    after `parse_path` on a real `.tac`."""
    return _apply("Apply", _sym("safe_math_narrow_bv256:bif"), arg)


def _run(cmds: list[TacCmd]):
    return analyze_types(TacProgram(blocks=[_block("B0", [], cmds)]))


def test_select_index_meets_to_ptr() -> None:
    res = _run([
        _havoc("M"),
        _havoc("R"),
        _assign("V", _apply("Select", _sym("M"), _sym("R"))),
    ])
    assert res.kind["R"] == TypeKind.PTR


def test_store_index_meets_to_ptr() -> None:
    res = _run([
        _havoc("M"),
        _havoc("R"),
        _havoc("V"),
        _assign("M2", _apply("Store", _sym("M"), _sym("R"), _sym("V"))),
    ])
    assert res.kind["R"] == TypeKind.PTR


def test_mul_operand_meets_to_int() -> None:
    res = _run([
        _havoc("R"),
        _havoc("S"),
        _assign("X", _apply("Mul", _sym("R"), _sym("S"))),
    ])
    assert res.kind["R"] == TypeKind.INT
    assert res.kind["S"] == TypeKind.INT
    assert res.kind["X"] == TypeKind.INT


def test_intdiv_operand_meets_to_int() -> None:
    res = _run([
        _havoc("R"),
        _assign("X", _apply("IntDiv", _sym("R"), _const("8"))),
    ])
    assert res.kind["R"] == TypeKind.INT


def test_shift_operand_meets_to_int() -> None:
    res = _run([
        _havoc("R"),
        _assign("X", _apply("ShiftLeft", _sym("R"), _const("3"))),
    ])
    assert res.kind["R"] == TypeKind.INT


def test_bwxor_operand_meets_to_int() -> None:
    res = _run([
        _havoc("R"),
        _havoc("S"),
        _assign("X", _apply("BWXOr", _sym("R"), _sym("S"))),
    ])
    assert res.kind["R"] == TypeKind.INT
    assert res.kind["S"] == TypeKind.INT


def test_constants_do_not_seed_kind() -> None:
    """A literal `0x300000538` (a region-prefix-shaped number) does not
    force the lhs to `Ptr`; pointer kind only flows from structural use."""
    res = _run([_assign("R", _const("0x300000538"))])
    assert res.kind["R"] == TypeKind.TOP


def test_constant_used_as_index_then_arithmetic_is_bot() -> None:
    """If the same canonical class has structural evidence both for `Ptr`
    (used as Select index) and `Int` (operand of Mul), the class is Bot."""
    res = _run([
        _havoc("M"),
        _assign("R", _const("0x300000538")),
        _assign("V1", _apply("Select", _sym("M"), _sym("R"))),
        _assign("V2", _apply("Mul", _sym("R"), _const("4"))),
    ])
    assert res.kind["R"] == TypeKind.BOT


def test_copy_unifies_classes() -> None:
    """`R' = SymRef(R)` puts both in the same class."""
    res = _run([
        _havoc("M"),
        _havoc("R"),
        _assign("R2", _sym("R")),
        # Use R2 as a Select index — should propagate to R via the union.
        _assign("V", _apply("Select", _sym("M"), _sym("R2"))),
    ])
    assert res.kind["R"] == TypeKind.PTR
    assert res.kind["R2"] == TypeKind.PTR
    assert res.class_id["R"] == res.class_id["R2"]


def test_narrow_passthrough_unifies() -> None:
    res = _run([
        _havoc("M"),
        _havoc("R"),
        _assign("R2", _narrow(_sym("R"))),
        _assign("V", _apply("Select", _sym("M"), _sym("R2"))),
    ])
    assert res.kind["R"] == TypeKind.PTR
    assert res.kind["R2"] == TypeKind.PTR
    assert res.class_id["R"] == res.class_id["R2"]


def test_bwand_with_const_is_passthrough() -> None:
    """`R2 = BWAnd(R, 0xfff...8)` (alignment) preserves R's kind."""
    res = _run([
        _havoc("M"),
        _havoc("R"),
        _assign("R2", _apply("BWAnd", _sym("R"), _const("0xfffffffffffffff8"))),
        _assign("V", _apply("Select", _sym("M"), _sym("R2"))),
    ])
    assert res.kind["R"] == TypeKind.PTR
    assert res.kind["R2"] == TypeKind.PTR


def test_assume_equality_unifies() -> None:
    """`assume R == R'` puts both in the same class."""
    res = _run([
        _havoc("M"),
        _havoc("R"),
        _havoc("R2"),
        _assume(_apply("Eq", _sym("R"), _sym("R2"))),
        _assign("V", _apply("Select", _sym("M"), _sym("R"))),
    ])
    assert res.kind["R"] == TypeKind.PTR
    assert res.kind["R2"] == TypeKind.PTR
    assert res.class_id["R"] == res.class_id["R2"]


def test_assume_equality_with_const_does_not_seed_kind() -> None:
    res = _run([
        _havoc("R"),
        _assume(_apply("Eq", _sym("R"), _const("0x300000000"))),
    ])
    assert res.kind["R"] == TypeKind.TOP


def test_add_ptr_plus_int_is_ptr() -> None:
    """`R = Add(p, off)` where p is Ptr (from index use) and off is Int
    (from Mul operand) — result is Ptr."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _havoc("OFF"),
        # Pin P as Ptr and OFF as Int.
        _assign("V1", _apply("Select", _sym("M"), _sym("P"))),
        _assign("V2", _apply("Mul", _sym("OFF"), _const("4"))),
        _assign("R", _apply("Add", _sym("P"), _sym("OFF"))),
    ])
    assert res.kind["P"] == TypeKind.PTR
    assert res.kind["OFF"] == TypeKind.INT
    assert res.kind["R"] == TypeKind.PTR


def test_intadd_ptr_plus_int_is_ptr() -> None:
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _havoc("OFF"),
        _assign("V1", _apply("Select", _sym("M"), _sym("P"))),
        _assign("V2", _apply("IntMul", _sym("OFF"), _const("8"))),
        _assign("R", _apply("IntAdd", _sym("P"), _sym("OFF"))),
    ])
    assert res.kind["R"] == TypeKind.PTR


def test_add_ptr_plus_small_const_is_ptr() -> None:
    """`R = Add(Rptr, small_const)` — recognizes the alignment / struct-
    field-offset pattern. R728 + 8 stays in the same (or adjacent) region."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _assign("V", _apply("Select", _sym("M"), _sym("P"))),
        _assign("R", _apply("Add", _sym("P"), _const("0x8"))),
    ])
    assert res.kind["P"] == TypeKind.PTR
    assert res.kind["R"] == TypeKind.PTR


def test_add_small_const_plus_ptr_is_ptr() -> None:
    """Argument order doesn't matter: small_const + Ptr is also Ptr."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _assign("V", _apply("Select", _sym("M"), _sym("P"))),
        _assign("R", _apply("IntAdd", _const("0x8"), _sym("P"))),
    ])
    assert res.kind["R"] == TypeKind.PTR


def test_sub_ptr_minus_small_const_is_ptr() -> None:
    """`R = Sub(Rptr, small_const)` — backward pointer arithmetic."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _assign("V", _apply("Select", _sym("M"), _sym("P"))),
        _assign("R", _apply("IntSub", _sym("P"), _const("0x10"))),
    ])
    assert res.kind["R"] == TypeKind.PTR


def test_sub_small_const_minus_ptr_stays_top() -> None:
    """`Sub(small_const, Ptr)` is not a sensible pointer in any semantics —
    the analysis abstains rather than concluding Ptr."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _assign("V", _apply("Select", _sym("M"), _sym("P"))),
        _assign("R", _apply("IntSub", _const("0x100"), _sym("P"))),
    ])
    assert res.kind["P"] == TypeKind.PTR
    assert res.kind["R"] == TypeKind.TOP


def test_sub_ptr_minus_int_is_ptr() -> None:
    """`Sub(Ptr, Int)` (with both as registers) — pointer minus offset."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _havoc("OFF"),
        _assign("V1", _apply("Select", _sym("M"), _sym("P"))),
        _assign("V2", _apply("Mul", _sym("OFF"), _const("4"))),
        _assign("R", _apply("Sub", _sym("P"), _sym("OFF"))),
    ])
    assert res.kind["P"] == TypeKind.PTR
    assert res.kind["OFF"] == TypeKind.INT
    assert res.kind["R"] == TypeKind.PTR


def test_add_ptr_plus_large_const_stays_top() -> None:
    """A constant whose magnitude is at or above the region-distance
    threshold (2^32) is not "small" — abstain to preserve soundness on
    region boundaries we can't reason about. ``ctac rw``-lifted bv ops
    like ``IntAdd(0x300000000, R)`` should not be confused with pointer
    arithmetic."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _assign("V", _apply("Select", _sym("M"), _sym("P"))),
        # 0x100000000 = 2^32, exactly the threshold — not "small".
        _assign("R", _apply("IntAdd", _sym("P"), _const("0x100000000"))),
    ])
    assert res.kind["P"] == TypeKind.PTR
    assert res.kind["R"] == TypeKind.TOP


def test_add_ptr_plus_negative_small_const_is_ptr() -> None:
    """Negative offsets are also small if their magnitude is below the
    threshold (e.g. backward struct-field math). The threshold uses
    ``abs(c)`` so negatives qualify symmetrically with positives."""
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _assign("V", _apply("Select", _sym("M"), _sym("P"))),
        # Decimal form: const_expr_to_int handles bare negative decimal
        # but not bare negative hex; the rule's threshold logic uses
        # abs(value), so the parsing form is what matters here.
        _assign("R", _apply("IntAdd", _sym("P"), _const("-16"))),
    ])
    assert res.kind["R"] == TypeKind.PTR


def test_narrow_add_chain_propagates_ptr_kind() -> None:
    """The TAC-typical chain `R = narrow(c +int Rptr)` now propagates
    the pointer kind even when R has no downstream index use."""
    res = _run([
        _havoc("M"),
        _havoc("BASE"),
        _assign("V", _apply("Select", _sym("M"), _sym("BASE"))),
        # R = narrow(0x8 +int BASE) — no downstream index use of R.
        _assign(
            "R",
            _narrow(_apply("IntAdd", _const("0x8"), _sym("BASE"))),
        ),
    ])
    assert res.kind["BASE"] == TypeKind.PTR
    assert res.kind["R"] == TypeKind.PTR


def test_add_int_plus_int_is_int() -> None:
    """`Int + Int = Int` is sound (no boundary-crossing risk) and is
    resolved by the v1 arithmetic-result rules."""
    res = _run([
        _havoc("A"),
        _havoc("B"),
        _assign("X1", _apply("Mul", _sym("A"), _const("2"))),
        _assign("X2", _apply("Mul", _sym("B"), _const("2"))),
        _assign("R", _apply("Add", _sym("A"), _sym("B"))),
    ])
    assert res.kind["A"] == TypeKind.INT
    assert res.kind["B"] == TypeKind.INT
    assert res.kind["R"] == TypeKind.INT


def test_intsub_int_minus_int_is_int() -> None:
    """`Int - Int = Int` — covers the I1503 = IntSub(R1774, R1460) pattern
    in `request_elevation_group`'s post-rw form."""
    res = _run([
        _havoc("A"),
        _havoc("B"),
        # Pin both as Int via downstream Mul use.
        _assign("X1", _apply("Mul", _sym("A"), _const("2"))),
        _assign("X2", _apply("Mul", _sym("B"), _const("2"))),
        _assign("I", _apply("IntSub", _sym("A"), _sym("B"))),
    ])
    assert res.kind["A"] == TypeKind.INT
    assert res.kind["B"] == TypeKind.INT
    assert res.kind["I"] == TypeKind.INT


def test_intadd_int_plus_small_const_is_int() -> None:
    """A small constant in arithmetic position acts as Int — propagating
    through `Int + small_const` to give an Int result. Constants are
    still NOT seeded with a kind globally (they can act as Int in one
    position and Ptr-context-receiving in another)."""
    res = _run([
        _havoc("R"),
        _assign("X", _apply("Mul", _sym("R"), _const("2"))),
        _assign("Y", _apply("IntAdd", _sym("R"), _const("0x10"))),
    ])
    assert res.kind["R"] == TypeKind.INT
    assert res.kind["Y"] == TypeKind.INT


def test_intsub_int_minus_small_const_is_int() -> None:
    res = _run([
        _havoc("R"),
        _assign("X", _apply("Mul", _sym("R"), _const("2"))),
        _assign("Y", _apply("IntSub", _sym("R"), _const("0x10"))),
    ])
    assert res.kind["R"] == TypeKind.INT
    assert res.kind["Y"] == TypeKind.INT


def test_intadd_two_small_consts_resolves_int() -> None:
    """Both operands small consts → Int+Int → Int. Edge case, but
    confirms the small-const-as-Int treatment composes."""
    res = _run([
        _havoc("M"),
        _assign("Y", _apply("IntAdd", _const("0x10"), _const("0x20"))),
        # Without a downstream use Y would already be Int via the rule.
        _assign("V", _apply("Select", _sym("M"), _sym("Y"))),
    ])
    # Y was used as a Select index → meet with Ptr would conflict with
    # the small-const-derived Int → Bot. This pins the soundness of the
    # small-const-as-Int treatment: it doesn't shield the result from
    # downstream contradictions.
    assert res.kind["Y"] == TypeKind.BOT


def test_ite_join_of_two_ptrs_is_ptr() -> None:
    res = _run([
        _havoc("M"),
        _havoc("P1"),
        _havoc("P2"),
        _havoc("C"),
        _assign("V1", _apply("Select", _sym("M"), _sym("P1"))),
        _assign("V2", _apply("Select", _sym("M"), _sym("P2"))),
        _assign("R", _apply("Ite", _sym("C"), _sym("P1"), _sym("P2"))),
    ])
    assert res.kind["P1"] == TypeKind.PTR
    assert res.kind["P2"] == TypeKind.PTR
    assert res.kind["R"] == TypeKind.PTR


def test_ite_join_of_ptr_and_int_is_top() -> None:
    res = _run([
        _havoc("M"),
        _havoc("P"),
        _havoc("I"),
        _havoc("C"),
        _assign("V1", _apply("Select", _sym("M"), _sym("P"))),
        _assign("V2", _apply("Mul", _sym("I"), _const("2"))),
        _assign("R", _apply("Ite", _sym("C"), _sym("P"), _sym("I"))),
    ])
    assert res.kind["P"] == TypeKind.PTR
    assert res.kind["I"] == TypeKind.INT
    assert res.kind["R"] == TypeKind.TOP


def test_loaded_value_is_top() -> None:
    """`R = M[idx]` — R is the value at idx, kind unconstrained."""
    res = _run([
        _havoc("M"),
        _havoc("IDX"),
        _assign("R", _apply("Select", _sym("M"), _sym("IDX"))),
    ])
    assert res.kind["IDX"] == TypeKind.PTR
    assert res.kind["R"] == TypeKind.TOP


def test_havoc_with_no_use_stays_top() -> None:
    """A havoc'd register with no structural use stays Top."""
    res = _run([_havoc("R")])
    assert res.kind["R"] == TypeKind.TOP


def test_chained_narrow_add_with_eventual_index_use() -> None:
    """Mirror of the target-file pattern: `R747 = narrow(8 +int R728)`,
    then `M[R747]`. R747 should land Ptr via index use; R728 stays Ptr
    if it's *also* used as an index. The narrow-add chain itself doesn't
    propagate Ptr backwards through the constant in v1 (sound, imprecise)."""
    res = _run([
        _havoc("M"),
        _havoc("R728"),
        _assign("V_BASE", _apply("Select", _sym("M"), _sym("R728"))),
        _assign(
            "R747",
            _narrow(_apply("IntAdd", _const("8"), _sym("R728"))),
        ),
        _assign("V_OFF", _apply("Select", _sym("M"), _sym("R747"))),
    ])
    assert res.kind["R728"] == TypeKind.PTR
    assert res.kind["R747"] == TypeKind.PTR


def test_assert_inside_walks_for_meets() -> None:
    """Hard meets fire on Select/Mul appearing inside AssertCmd predicates
    too (sound: the position constraints don't depend on whether the
    expression is in an assign / assume / assert)."""
    program = TacProgram(blocks=[
        _block("B0", [], [
            _havoc("M"),
            _havoc("R"),
            AssertCmd(
                raw="assert ...",
                predicate=_apply("Eq", _apply("Select", _sym("M"), _sym("R")), _const("1")),
                message=None,
            ),
        ])
    ])
    res = analyze_types(program)
    assert res.kind["R"] == TypeKind.PTR


def test_class_members_grouping() -> None:
    """Equality-unified registers report under the same class root."""
    res = _run([
        _havoc("R"),
        _assign("R2", _sym("R")),
        _assign("R3", _narrow(_sym("R2"))),
    ])
    assert res.class_id["R"] == res.class_id["R2"] == res.class_id["R3"]
    members = res.class_members[res.class_id["R"]]
    assert set(members) == {"R", "R2", "R3"}


def test_dsa_suffix_is_canonicalized() -> None:
    """Symbols that differ only by `:N` DSA suffix are the same class."""
    res = _run([
        _havoc("M"),
        _assign("R:1", _const("0x300000000")),
        _assign("V", _apply("Select", _sym("M"), _sym("R:2"))),
    ])
    # Both `R:1` and `R:2` canonicalize to `R`.
    assert res.kind["R"] == TypeKind.PTR


def test_iterations_converge_finite() -> None:
    """Pin that the fixpoint terminates (no infinite loop on a small program)."""
    res = _run([
        _havoc("M"),
        _havoc("R"),
        _assign("V", _apply("Select", _sym("M"), _sym("R"))),
    ])
    # Lattice depth is 3, a few iterations suffice.
    assert 1 <= res.iterations <= 5


def test_trace_sink_emits_structural_meet_events() -> None:
    """Trace should record the Ptr-meet at the Select-index site."""
    from ctac.analysis.type_infer import TypeTraceEntry, analyze_types
    from ctac.ir.models import TacProgram

    events: list[TypeTraceEntry] = []
    program = TacProgram(blocks=[
        _block("B0", [], [
            _havoc("M"),
            _havoc("R"),
            _assign("V", _apply("Select", _sym("M"), _sym("R"))),
        ])
    ])
    analyze_types(program, trace_sink=events.append)
    # Must include a select-index meet event that promotes R from Top to Ptr.
    select_meets = [
        e for e in events
        if e.rule == "select-index" and "R" in e.symbols
    ]
    assert select_meets, "expected a select-index meet event for R"
    promoted = [e for e in select_meets if e.changed and e.before == "Top" and e.after == "Ptr"]
    assert promoted, f"expected at least one Top->Ptr meet; got {select_meets!r}"


def test_trace_sink_emits_rhs_eval_for_each_assign_each_iteration() -> None:
    """Per-AssignExpCmd RHS-eval summary fires every iteration so users can
    see what kind the RHS resolved to (the diagnostic for `Top` outcomes)."""
    from ctac.analysis.type_infer import TypeTraceEntry, analyze_types
    from ctac.ir.models import TacProgram

    events: list[TypeTraceEntry] = []
    program = TacProgram(blocks=[
        _block("B0", [], [
            _havoc("M"),
            _havoc("R"),
            _assign("V", _apply("Select", _sym("M"), _sym("R"))),
        ])
    ])
    res = analyze_types(program, trace_sink=events.append)
    rhs_evals = [e for e in events if e.kind == "rhs-eval" and "V" in e.symbols]
    # One rhs-eval per iteration for V.
    assert len(rhs_evals) == res.iterations, (
        f"expected {res.iterations} rhs-eval events for V, got {len(rhs_evals)}"
    )


def test_trace_sink_emits_union_event_on_copy() -> None:
    from ctac.analysis.type_infer import TypeTraceEntry, analyze_types
    from ctac.ir.models import TacProgram

    events: list[TypeTraceEntry] = []
    program = TacProgram(blocks=[
        _block("B0", [], [
            _havoc("R"),
            _assign("R2", _sym("R")),
        ])
    ])
    analyze_types(program, trace_sink=events.append)
    unions = [e for e in events if e.kind == "union" and e.rule == "copy-assign"]
    assert unions, "expected at least one copy-assign union event"
    e = unions[0]
    assert set(e.symbols) == {"R", "R2"}
    assert e.changed is True


def test_trace_sink_silent_when_class_already_at_kind() -> None:
    """A meet that doesn't change anything still emits a record with
    ``changed=false`` — needed so consumers can see no-op attempts (the
    'why didn't this tighten?' diagnostic)."""
    from ctac.analysis.type_infer import TypeTraceEntry, analyze_types
    from ctac.ir.models import TacProgram

    events: list[TypeTraceEntry] = []
    program = TacProgram(blocks=[
        _block("B0", [], [
            _havoc("M"),
            _havoc("R"),
            # Two redundant select-index uses — second meet is a no-op.
            _assign("V1", _apply("Select", _sym("M"), _sym("R"))),
            _assign("V2", _apply("Select", _sym("M"), _sym("R"))),
        ])
    ])
    analyze_types(program, trace_sink=events.append)
    no_change_meets = [
        e for e in events
        if e.kind == "meet" and e.rule == "select-index" and not e.changed
    ]
    assert no_change_meets, "expected a no-change select-index meet event"
