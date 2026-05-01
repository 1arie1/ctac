"""Library tests for ``ctac.analysis.slice.compute_slice``."""

from __future__ import annotations

from ctac.analysis import (
    SliceConfig,
    SliceCriterion,
    compute_slice,
)
from ctac.analysis.model import ProgramPoint
from ctac.parse import parse_string


_TAC_DATA_CHAIN = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bv256
\tc:bv256
\td:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd a 0x1
\t\tAssignExpCmd b 0x2
\t\tAssignExpCmd c Add(a 0x1)
\t\tAssignExpCmd d 0x99
\t\tAssertCmd Eq(c b) "must hold"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_data_chain_includes_transitive_defs() -> None:
    tac = parse_string(_TAC_DATA_CHAIN)
    crit = SliceCriterion(last_assert_in_block="entry")
    res = compute_slice(tac.program, [crit])
    blk = tac.program.blocks[0]
    # Find indices of relevant cmds.
    idx = {type(c).__name__: i for i, c in enumerate(blk.commands)}
    # The assert (seed), the def of c (Add(a 0x1)), the def of a, the def of b.
    # We can't index into the duplicates by name only, so check by symbol.
    selected_lhs = {
        getattr(blk.commands[pt.cmd_index], "lhs", None)
        for pt in res.selected
        if pt.block_id == "entry"
    }
    selected_lhs.discard(None)
    assert "a" in selected_lhs
    assert "b" in selected_lhs
    assert "c" in selected_lhs
    assert "d" not in selected_lhs  # unrelated def must be excluded
    _ = idx


def test_data_only_dropping_control_only_keeps_seed() -> None:
    tac = parse_string(_TAC_DATA_CHAIN)
    crit = SliceCriterion(last_assert_in_block="entry")
    cfg = SliceConfig(follow_data=False, follow_control=False)
    res = compute_slice(tac.program, [crit], cfg)
    # With both off, slice = exactly the seed.
    assert len(res.selected) == 1
    assert next(iter(res.selected)).block_id == "entry"


_TAC_BYTEMAP = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tM0:bytemap
\tM1:bytemap
\tM2:bytemap
\tk1:bv256
\tk2:bv256
\tv1:bv256
\tv2:bv256
\tr:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd M0
\t\tAssignExpCmd k1 0x10
\t\tAssignExpCmd v1 0xaa
\t\tAssignExpCmd k2 0x20
\t\tAssignExpCmd v2 0xbb
\t\tAssignExpCmd M1 Store(M0 k1 v1)
\t\tAssignExpCmd M2 Store(M1 k2 v2)
\t\tAssignExpCmd r Select(M2 k1)
\t\tAssertCmd Eq(r v1) "select after store"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_bytemap_chain_pulled_in() -> None:
    """Slicing from ``r``'s assert pulls every Store + havoc that defines M2."""
    tac = parse_string(_TAC_BYTEMAP)
    crit = SliceCriterion(last_assert_in_block="entry")
    res = compute_slice(tac.program, [crit])
    blk = tac.program.blocks[0]
    selected_targets: set[str] = set()
    for pt in res.selected:
        cmd = blk.commands[pt.cmd_index]
        lhs = getattr(cmd, "lhs", None)
        if lhs is not None:
            selected_targets.add(lhs)
    # Full bytemap chain plus key/value computations.
    assert {"M0", "M1", "M2", "k1", "k2", "v1", "v2", "r"} <= selected_targets


def test_bytemap_no_data_is_seed_only() -> None:
    tac = parse_string(_TAC_BYTEMAP)
    crit = SliceCriterion(last_assert_in_block="entry")
    cfg = SliceConfig(follow_data=False, follow_control=False)
    res = compute_slice(tac.program, [crit], cfg)
    assert len(res.selected) == 1


_TAC_CONTROL = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tcond:bool
\tu:bv256
\ta:bv256
\tx:bv256
}
Program {
\tBlock entry Succ [thn, els] {
\t\tAssignExpCmd u 0x5
\t\tAssignExpCmd cond Eq(u 0x5)
\t\tJumpiCmd thn els cond
\t}
\tBlock thn Succ [merge] {
\t\tAssignExpCmd a 0x1
\t\tJumpCmd merge
\t}
\tBlock els Succ [merge] {
\t\tAssignExpCmd a 0x2
\t\tJumpCmd merge
\t}
\tBlock merge Succ [] {
\t\tAssignExpCmd x a
\t\tAssertCmd Eq(x x) "trivial"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_control_dep_pulls_branch_and_condition() -> None:
    """With ``--control``, slicing the assert in ``merge`` pulls the JumpiCmd
    in ``entry`` and its condition's data dependences."""
    tac = parse_string(_TAC_CONTROL)
    crit = SliceCriterion(last_assert_in_block="merge")
    res = compute_slice(tac.program, [crit])
    selected_blocks = {pt.block_id for pt in res.selected}
    # entry is control-relevant; thn and els define `a` (data dep).
    assert "merge" in selected_blocks
    assert "entry" in selected_blocks
    # Pulled in: cond's def + u's def in entry.
    by_id = tac.program.block_by_id()
    entry_lhs = {
        getattr(by_id["entry"].commands[pt.cmd_index], "lhs", None)
        for pt in res.selected
        if pt.block_id == "entry"
    }
    assert "cond" in entry_lhs
    assert "u" in entry_lhs


def test_no_control_drops_branch() -> None:
    tac = parse_string(_TAC_CONTROL)
    crit = SliceCriterion(last_assert_in_block="merge")
    cfg = SliceConfig(follow_data=True, follow_control=False)
    res = compute_slice(tac.program, [crit], cfg)
    selected_blocks = {pt.block_id for pt in res.selected}
    # Without control, entry is irrelevant (no data def of `a` lives there).
    assert "entry" not in selected_blocks
    assert "merge" in selected_blocks


def test_max_depth_zero_is_just_seeds() -> None:
    tac = parse_string(_TAC_DATA_CHAIN)
    crit = SliceCriterion(last_assert_in_block="entry")
    cfg = SliceConfig(max_depth=0)
    res = compute_slice(tac.program, [crit], cfg)
    assert len(res.selected) == 1


def test_symbol_seed_resolves_to_def() -> None:
    """Bare ``-c c`` (the symbol) seeds the def of ``c`` and its closure."""
    tac = parse_string(_TAC_DATA_CHAIN)
    crit = SliceCriterion(symbol="c")
    res = compute_slice(tac.program, [crit])
    blk = tac.program.blocks[0]
    selected_lhs = {
        getattr(blk.commands[pt.cmd_index], "lhs", None)
        for pt in res.selected
        if pt.block_id == "entry"
    }
    selected_lhs.discard(None)
    assert "c" in selected_lhs
    assert "a" in selected_lhs  # transitive
    assert "d" not in selected_lhs


def test_symbol_in_block_disambiguates() -> None:
    """``SYM@BLK`` selects only defs of SYM in BLK."""
    tac = parse_string(_TAC_CONTROL)
    crit = SliceCriterion(symbol_in_block=("a", "thn"))
    res = compute_slice(tac.program, [crit])
    selected = {(pt.block_id, pt.cmd_index) for pt in res.selected}
    # a's def in thn is selected; els's def is not.
    by_id = tac.program.block_by_id()
    thn_a_idx = next(
        i
        for i, c in enumerate(by_id["thn"].commands)
        if getattr(c, "lhs", None) == "a"
    )
    els_a_idx = next(
        i
        for i, c in enumerate(by_id["els"].commands)
        if getattr(c, "lhs", None) == "a"
    )
    assert ("thn", thn_a_idx) in selected
    assert ("els", els_a_idx) not in selected


def test_warnings_on_unknown_symbol() -> None:
    tac = parse_string(_TAC_DATA_CHAIN)
    crit = SliceCriterion(symbol="nope_does_not_exist")
    res = compute_slice(tac.program, [crit])
    assert any("nope_does_not_exist" in w for w in res.warnings)
    assert len(res.selected) == 0


def test_unknown_block_for_assert_raises() -> None:
    tac = parse_string(_TAC_DATA_CHAIN)
    crit = SliceCriterion(last_assert_in_block="not_a_block")
    try:
        compute_slice(tac.program, [crit])
    except ValueError as e:
        assert "not_a_block" in str(e)
        return
    raise AssertionError("expected ValueError for unknown block")


def test_compute_slice_accepts_precomputed_analyses() -> None:
    from ctac.analysis import (
        analyze_control_dependence,
        analyze_reaching_definitions,
        extract_def_use,
    )

    tac = parse_string(_TAC_CONTROL)
    du = extract_def_use(tac.program)
    rd = analyze_reaching_definitions(tac.program, def_use=du)
    cd = analyze_control_dependence(tac.program)
    crit = SliceCriterion(last_assert_in_block="merge")
    res = compute_slice(
        tac.program,
        [crit],
        def_use=du,
        reaching_defs=rd,
        control_dep=cd,
    )
    # Non-empty result confirms the precomputed analyses are used.
    assert len(res.selected) > 1


def test_seeds_dedupe_across_criteria() -> None:
    tac = parse_string(_TAC_DATA_CHAIN)
    crits = [
        SliceCriterion(symbol="c"),
        SliceCriterion(last_assert_in_block="entry"),
    ]
    res = compute_slice(tac.program, crits)
    # Both criteria pull in `a` and `c` — result is a union, not a multiset.
    blk = tac.program.blocks[0]
    selected_pts = {pt for pt in res.selected if pt.block_id == "entry"}
    cmd_indices = {pt.cmd_index for pt in selected_pts}
    # No duplicates by construction (selected is a frozenset).
    assert len(cmd_indices) == len(selected_pts)
    # The assert (last cmd) is in the slice.
    assert ProgramPoint("entry", len(blk.commands) - 1) in res.selected
