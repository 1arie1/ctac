from __future__ import annotations

from ctac.diff.match_cfg import compare_matched_blocks, match_cfg_blocks
from ctac.parse import parse_string


TAC_LEFT = """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	R1:bv256
}
Program {
	Block A Succ [B, C] {
		AssignExpCmd R1 0x1
	}
	Block B Succ [D] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"verification.certora.TACSnippetCmd$CexPrintTag","displayMessage":"tag-b"}}
		AssignExpCmd R1 Add(R1 0x2)
	}
	Block C Succ [D] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"verification.certora.TACSnippetCmd$CexPrintTag","displayMessage":"tag-c"}}
		AssignExpCmd R1 Add(R1 0x3)
	}
	Block D Succ [] {
		AssertCmd R1 "done"
	}
}
Axioms {
}
Metas {
  "0": []
}
"""


TAC_RIGHT = """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	R10:bv256
}
Program {
	Block X Succ [Y, Z] {
		AssignExpCmd R10 0x1
	}
	Block Y Succ [W] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"verification.certora.TACSnippetCmd$CexPrintTag","displayMessage":"tag-b"}}
		AssignExpCmd R10 Add(R10 0x2)
	}
	Block Z Succ [W] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"verification.certora.TACSnippetCmd$CexPrintTag","displayMessage":"tag-c"}}
		AssignExpCmd R10 Add(R10 0x3)
	}
	Block W Succ [] {
		AssertCmd R10 "done"
	}
}
Axioms {
}
Metas {
  "0": []
}
"""


TAC_RIGHT_CHANGED = """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	R10:bv256
}
Program {
	Block X Succ [Y, Z] {
		AssignExpCmd R10 0x1
	}
	Block Y Succ [W] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"verification.certora.TACSnippetCmd$CexPrintTag","displayMessage":"tag-b"}}
		AssignExpCmd R10 Add(R10 0x9)
	}
	Block Z Succ [W] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"verification.certora.TACSnippetCmd$CexPrintTag","displayMessage":"tag-c"}}
		AssignExpCmd R10 Add(R10 0x3)
	}
	Block W Succ [] {
		AssertCmd R10 "done"
	}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_match_cfg_uses_structure_and_tags() -> None:
    left = parse_string(TAC_LEFT, path="<left>")
    right = parse_string(TAC_RIGHT, path="<right>")
    res = match_cfg_blocks(left, right, min_score=0.35)
    pairs = {(m.left_id, m.right_id) for m in res.matches}
    assert ("A", "X") in pairs
    assert ("B", "Y") in pairs
    assert ("C", "Z") in pairs
    assert ("D", "W") in pairs
    assert not res.unmatched_left
    assert not res.unmatched_right


def test_compare_matched_blocks_detects_local_delta() -> None:
    left = parse_string(TAC_LEFT, path="<left>")
    right = parse_string(TAC_RIGHT_CHANGED, path="<right>")
    mr = match_cfg_blocks(left, right, min_score=0.35)
    comps = compare_matched_blocks(left, right, match_result=mr, normalize_vars=True, include_source=False)
    by_pair = {(c.left_id, c.right_id): c for c in comps}
    assert ("B", "Y") in by_pair
    assert by_pair[("B", "Y")].changed
    assert any("0x2" in ln or "0x9" in ln for ln in by_pair[("B", "Y")].diff_lines)
    assert ("C", "Z") in by_pair
    assert not by_pair[("C", "Z")].changed


def test_compare_matched_blocks_ignores_empty_when_requested() -> None:
    left = parse_string(
        """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	R1:bv256
}
Program {
	Block A Succ [] {
		LabelCmd "x"
		AssignExpCmd R1 0x1
	}
}
Axioms {
}
Metas {
  "0": []
}
""",
        path="<left-empty>",
    )
    right = parse_string(
        """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	R2:bv256
}
Program {
	Block B Succ [] {
		AssignExpCmd R2 0x1
	}
}
Axioms {
}
Metas {
  "0": []
}
""",
        path="<right-empty>",
    )
    mr = match_cfg_blocks(left, right, min_score=0.2)
    comps = compare_matched_blocks(
        left,
        right,
        match_result=mr,
        normalize_vars=True,
        include_source=False,
        drop_empty_lines=True,
    )
    assert len(comps) == 1
    assert not comps[0].changed


def test_match_cfg_disambiguates_swapped_blocks_by_constants() -> None:
    left = parse_string(
        """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	R1:bv256
	B1:bool
	B2:bool
}
Program {
	Block E Succ [B, C] {
		AssignExpCmd R1 0x1
	}
	Block B Succ [X] {
		AssignExpCmd B1 Eq(0xffffffffffffffffffffffffffffffffffffffffffffffffac79ebce46e1cbd9 R1)
	}
	Block C Succ [X] {
		AssignExpCmd B2 Eq(0xffffffffffffffffffffffffffffffffffffffffffffffffa900ff7e85f58c3a R1)
	}
	Block X Succ [] {
		AssertCmd B1 "done"
	}
}
Axioms {
}
Metas {
  "0": []
}
""",
        path="<left-swap>",
    )
    right = parse_string(
        """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	R9:bv256
	B7:bool
	B8:bool
}
Program {
	Block E2 Succ [Y, Z] {
		AssignExpCmd R9 0x1
	}
	Block Y Succ [W] {
		AssignExpCmd B7 Eq(0xffffffffffffffffffffffffffffffffffffffffffffffffa900ff7e85f58c3a R9)
	}
	Block Z Succ [W] {
		AssignExpCmd B8 Eq(0xffffffffffffffffffffffffffffffffffffffffffffffffac79ebce46e1cbd9 R9)
	}
	Block W Succ [] {
		AssertCmd B7 "done"
	}
}
Axioms {
}
Metas {
  "0": []
}
""",
        path="<right-swap>",
    )
    mr_no_const = match_cfg_blocks(left, right, min_score=0.2, const_weight=0.0)
    pairs_no_const = {(m.left_id, m.right_id) for m in mr_no_const.matches}
    # With no const signal, ties follow structural order and can cross-pair.
    assert ("B", "Y") in pairs_no_const
    assert ("C", "Z") in pairs_no_const

    mr = match_cfg_blocks(left, right, min_score=0.2, const_weight=0.2)
    pairs = {(m.left_id, m.right_id) for m in mr.matches}
    assert ("B", "Z") in pairs
    assert ("C", "Y") in pairs

