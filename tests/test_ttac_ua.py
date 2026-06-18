import pytest

import ttac_fixtures as fx
from ctac.ttac import ast, parse_program, pretty
from ctac.ttac.analysis import check_dsa, infer_types
from ctac.ttac.transform.ua import (
    ERROR_BLOCK,
    merge_asserts,
    split_asserts,
)


def all_asserts(program):
    return [
        c for b in program.blocks for c in b.commands if isinstance(c, ast.Assert)
    ]


# --- merge ---


def test_merge_two_asserts_single_assert_in_error_block():
    res = merge_asserts(parse_program(fx.TWO_ASSERTS))
    assert res.asserts_merged == 2
    assert not res.was_noop
    asserts = all_asserts(res.program)
    assert len(asserts) == 1
    err = [b for b in res.program.blocks if b.label == ERROR_BLOCK][0]
    assert asserts[0] in err.commands


def test_merge_block_structure_and_floyd_hoare():
    res = merge_asserts(parse_program(fx.TWO_ASSERTS))
    labels = [b.label for b in res.program.blocks]
    assert labels == [
        "entry", "entry_UA0_land", "entry_UA0", "entry_UA1_land", "entry_UA1",
        ERROR_BLOCK,
    ]
    entry = res.program.blocks[0]
    assert entry.terminator == ast.IfGoto("a", "entry_UA0", "entry_UA0_land")
    cont = [b for b in res.program.blocks if b.label == "entry_UA0"][0]
    assert cont.commands[0] == ast.Assume(ast.Var("a"))  # Floyd-Hoare


def test_merge_output_is_wellformed_and_typed():
    res = merge_asserts(parse_program(fx.TWO_ASSERTS))
    assert check_dsa(res.program).is_valid
    t = infer_types(res.program)
    assert t["a"] == ast.Ty.BOOL and t["b"] == ast.Ty.BOOL
    assert parse_program(pretty(res.program)) == res.program


def test_merge_single_assert_is_noop():
    res = merge_asserts(parse_program(fx.CORE))
    assert res.was_noop
    assert res.program == parse_program(fx.CORE)


def test_merge_zero_asserts_is_noop():
    res = merge_asserts(parse_program("entry:\n  x := havoc\n  halt\n"))
    assert res.was_noop


def test_merge_collision_raises():
    src = (
        "entry:\n  a := havoc\n  b := havoc\n  assert a\n  assert b\n"
        "  goto __UA_ERROR\n\n__UA_ERROR:\n  halt\n"
    )
    with pytest.raises(ValueError, match="already exists"):
        merge_asserts(parse_program(src))


# --- split ---


def test_split_one_output_per_assert():
    res = split_asserts(parse_program(fx.BRANCH_ASSERTS))
    assert res.asserts_before == 2
    assert len(res.outputs) == 2
    for out in res.outputs:
        assert len(all_asserts(out.program)) == 1


def test_split_polarity_then_and_else():
    res = split_asserts(parse_program(fx.BRANCH_ASSERTS))
    by_block = {o.block: o for o in res.outputs}
    l_assumes = [
        c.cond for b in by_block["L"].program.blocks for c in b.commands
        if isinstance(c, ast.Assume)
    ]
    r_assumes = [
        c.cond for b in by_block["R"].program.blocks for c in b.commands
        if isinstance(c, ast.Assume)
    ]
    assert ast.Assume(ast.Var("c")).cond in l_assumes
    assert ast.UnExpr("not", ast.Var("c")) in r_assumes


def test_split_outputs_wellformed():
    # Each per-assert program is structurally well-formed and round-trips.
    # (Type totality is not guaranteed: COI pruning can leave a havoc'd
    # variable unused in an arm where it was only read by the other arm.)
    res = split_asserts(parse_program(fx.BRANCH_ASSERTS))
    for out in res.outputs:
        assert check_dsa(out.program).is_valid
        assert parse_program(pretty(out.program)) == out.program


def test_split_zero_asserts_is_noop():
    res = split_asserts(parse_program("entry:\n  x := havoc\n  halt\n"))
    assert res.was_noop and res.outputs == ()


def test_split_single_assert():
    res = split_asserts(parse_program(fx.CORE))
    assert res.asserts_before == 1
    assert len(res.outputs) == 1
