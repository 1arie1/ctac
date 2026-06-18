import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.run import RunConfig, run_program


def run(src, **kw):
    return run_program(parse_program(src), config=RunConfig(**kw))


def test_arithmetic_with_zero_havoc():
    r = run("entry:\n  x := havoc\n  y := x + 1\n  ok := y == 1\n  assert ok\n  halt\n")
    assert r.status == "done"
    assert r.assert_ok == 1 and r.assert_fail == 0
    assert r.final_store["y"].data == 1


def test_assert_failure_counts_and_continues():
    r = run("entry:\n  b := havoc\n  assert b\n  halt\n")  # b havoc-zero -> false
    assert r.status == "done"
    assert r.assert_fail == 1


def test_assume_false_stops():
    r = run("entry:\n  b := havoc\n  assume b\n  halt\n")
    assert r.status == "stopped"
    assert "assume" in r.reason


def test_bytemap_store_then_load():
    r = run(
        "entry:\n  M := havoc\n  i := havoc\n  M2 := M[i := 7]\n  x := M2[i]\n"
        "  ok := x == 7\n  assert ok\n  halt\n"
    )
    assert r.status == "done"
    assert r.final_store["x"].data == 7
    assert r.assert_ok == 1


def test_branch_taken_by_condition():
    # c = (0 <= 1) = true -> goto yes; assert in yes runs.
    src = (
        "entry:\n  c := 0 <= 1\n  if c goto yes else no\n\n"
        "yes:\n  ok := 0 <= 0\n  assert ok\n  halt\n\n"
        "no:\n  halt\n"
    )
    r = run(src)
    assert r.executed_blocks == ["entry", "yes"]
    assert r.assert_ok == 1


def test_phi_selects_by_predecessor():
    src = (
        "entry:\n  c := 0 <= 1\n  if c goto l else rr\n\n"
        "l:\n  a := havoc\n  goto j\n\n"
        "rr:\n  b := havoc\n  goto j\n\n"
        "j:\n  z := phi [l: a, rr: b]\n  ok := z == a\n  assert ok\n  halt\n"
    )
    r = run(src)
    # entry -> l (c true) -> j; phi picks the `l` arm (a).
    assert "l" in r.executed_blocks and r.assert_ok == 1


def test_borrow_free_run_stops_at_prophecy_assume():
    # Desugared mutable borrow: release's `assume value == promise` cannot
    # hold under zero-havoc (promise=0 != written value), so the run stops.
    r = run_program(parse_program(fx.MUT_BORROW_SURFACE))
    assert r.status == "stopped"
    assert "assume" in r.reason


def test_trace_annotates_memory_indices():
    src = (
        "entry:\n  M := havoc\n  i := havoc\n  M2 := M[i := 7]\n  x := M2[i]\n"
        "  ok := x == 7\n  assert ok\n  halt\n"
    )
    r = run(src)
    by_lhs = {ev.rendered: ev for ev in r.events}
    # Load shows the resolved index; store shows index := value.
    assert by_lhs["x := M2[i]"].mem == "M2[0]"
    assert by_lhs["x := M2[i]"].value.data == 7
    assert by_lhs["M2 := M[i := 7]"].mem == "M[0 := 7]"


def test_trace_terminator_branch_note():
    src = (
        "entry:\n  c := 0 <= 1\n  if c goto yes else no\n\n"
        "yes:\n  halt\n\nno:\n  halt\n"
    )
    r = run(src)
    term = next(ev for ev in r.events if ev.rendered.startswith("if "))
    assert "c=true" in term.note and "-> yes" in term.note


def test_division_is_euclidean():
    r = run("entry:\n  q := havoc\n  halt\n")  # warm-up; check eval via expression
    from ctac.ttac.run import _ediv

    assert _ediv(7, 2) == 3
    assert _ediv(-7, 2) == -4  # SMT-LIB: -7 = 2*(-4) + 1
    assert _ediv(5, 0) == 0
    assert r.status == "done"
