import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.stats import collect_stats, stats_to_dict


def stats(src):
    return stats_to_dict(collect_stats(parse_program(src)))


CONST_BORROW = (
    "entry:\n  M := havoc\n  i := havoc\n  p := borrow M[i]\n  x := get_ref p\n"
    "  release p\n  ok := x == x\n  assert ok\n  halt\n"
)

BYTEMAP_FREE = (
    "entry:\n  a := havoc\n  b := havoc\n  c := a <= b\n  assert c\n  halt\n"
)


def test_core_overview_and_capability():
    d = stats(fx.CORE)
    assert d["overview.blocks"] == 4
    assert d["overview.commands"] == 9
    assert d["terminator_kinds.IfGoto"] == 1
    assert d["memory.capability"] == "bytemap-rw"  # M[i := y] update
    assert d["references.reference_free"] == "true"
    assert d["shape.asserts"] == 1
    assert d["shape.loop_free"] == "true"


def test_borrow_surface_reference_counts():
    d = stats(fx.BORROW_SURFACE)
    assert d["references.reference_free"] == "false"
    assert d["references.ref_symbols"] == 3
    assert d["command_kinds.BorrowMut"] == 1
    assert d["references.borrow"] == 1
    assert d["references.borrow_mut"] == 1
    assert d["references.get_ref"] == 1
    assert d["references.put_ref"] == 1
    assert d["references.release"] == 2
    assert d["memory.capability"] == "bytemap-rw"  # mutable borrow writes


def test_const_borrow_is_bytemap_ro():
    d = stats(CONST_BORROW)
    assert d["memory.capability"] == "bytemap-ro"
    assert d["references.borrow"] == 1
    assert d["references.get_ref"] == 1
    assert d["references.release"] == 1
    assert "references.borrow_mut" not in d  # only emitted when present


def test_bytemap_free_program():
    d = stats(BYTEMAP_FREE)
    assert d["memory.capability"] == "bytemap-free"
    assert d["memory.bytemap_symbols"] == 0
    assert d["references.reference_free"] == "true"


def test_type_distribution():
    d = stats(fx.CORE)
    assert d["types.int"] == 4
    assert d["types.bool"] == 1
    assert d["types.bytemap"] == 2
    assert d["types.total"] == "true"


def test_nonlinear_counter():
    src = "entry:\n  a := havoc\n  b := havoc\n  c := a * b\n  ok := 0 <= c\n  assert ok\n  halt\n"
    d = stats(src)
    assert d["nonlinear_ops.multiplication"] == 1


def test_desugared_program_is_reference_free():
    from ctac.ttac.transform import desugar_refs

    desugared = desugar_refs(parse_program(fx.BORROW_SURFACE)).program
    d = stats_to_dict(collect_stats(desugared))
    assert d["references.reference_free"] == "true"
    assert "command_kinds.Borrow" not in d
