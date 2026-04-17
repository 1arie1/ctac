from __future__ import annotations

from ctac.diff.semantic import (
    collect_records,
    render_records,
    slice_records_to_assert_dependencies,
    unified_semantic_diff,
)
from ctac.parse import parse_string


TAC_A = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR1:bv256
\tR2:bv256
\tB1:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd R1 0x2
\t\tAssignExpCmd R2 Add(R1 0x3)
\t\tAssignExpCmd B1 Eq(R2 0x5)
\t\tAssertCmd B1 "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_B_RENUMBER = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR10:bv256
\tR20:bv256
\tB8:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd R10 0x2
\t\tAssignExpCmd R20 Add(R10 0x3)
\t\tAssignExpCmd B8 Eq(R20 0x5)
\t\tAssertCmd B8 "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_B_CHANGED = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR10:bv256
\tR20:bv256
\tB8:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd R10 0x2
\t\tAssignExpCmd R20 Add(R10 0x4)
\t\tAssignExpCmd B8 Eq(R20 0x5)
\t\tAssertCmd B8 "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _lines(tac_text: str) -> list[str]:
    tac = parse_string(tac_text, path="<string>")
    rec = collect_records(tac)
    rec = slice_records_to_assert_dependencies(rec)
    return render_records(rec, include_source=False, normalize_vars=True, include_block_id=False)


def test_normalized_diff_hides_pure_renaming() -> None:
    d = unified_semantic_diff(_lines(TAC_A), _lines(TAC_B_RENUMBER), a_name="a", b_name="b")
    assert d == []


def test_normalized_diff_reports_actual_expression_change() -> None:
    d = unified_semantic_diff(_lines(TAC_A), _lines(TAC_B_CHANGED), a_name="a", b_name="b")
    assert d
    assert any(" 3" in line or " 4" in line for line in d)

