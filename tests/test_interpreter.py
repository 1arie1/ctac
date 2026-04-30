from __future__ import annotations

from ctac.eval import RunConfig, Value, run_program
from ctac.parse import parse_string


RUN_TAC = """TACSymbolTable {
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
\tBlock entry Succ [ok, fail] {
\t\tAssignExpCmd R1 0x2
\t\tAssignHavocCmd R2
\t\tAssignExpCmd B1 Eq(R1 0x2)
\t\tJumpiCmd ok fail B1
\t}
\tBlock ok Succ [end] {
\t\tAssertCmd B1 "must hold"
\t\tJumpCmd end
\t}
\tBlock fail Succ [end] {
\t\tAssertCmd B1 "should fail"
\t\tJumpCmd end
\t}
\tBlock end Succ [] {
\t\tAssumeExpCmd Eq(R1 0x2)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


ASSUME_FAIL_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tB1:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd B1 false
\t\tAssumeExpCmd B1
\t\tAssertCmd B1 "unreachable"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


SUFFIX_REF_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR1:bv256
\tR2:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd R1 0x20
\t\tAssignExpCmd R2 Add(R1:5 0x7)
\t\tAssumeExpCmd Eq(R2 0x27)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


PRINT_SNIPPET_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR1:bv256
\tR2:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd R1 0x2
\t\tAssignExpCmd R2 0x3
\t\tAnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.ScopeStart","scopeName":"pre"}}
\t\tAnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.CexPrintValues","displayMessage":"x","symbols":[{"namePrefix":"R1"}]}}
\t\tAnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.CexPrint128BitsValue","displayMessage":"y","low":{"namePrefix":"R1"},"high":{"namePrefix":"R2"},"signed":false}}
\t\tAnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.CexPrintTag","displayMessage":"x <= y"}}
\t\tAnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.ScopeEnd","scopeName":"pre"}}
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

PRINT_SNIPPET_DANGLING_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR1:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd R1 0x2
\t\tAnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.CexPrintValues","displayMessage":"missing","symbols":[{"namePrefix":"R9"}]}}
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_run_zero_havoc_basic_flow() -> None:
    tac = parse_string(RUN_TAC, path="<string>")
    res = run_program(tac.program, config=RunConfig(havoc_mode="zero"))
    assert res.status == "done"
    assert "entry" in res.executed_blocks
    assert "fail" not in res.executed_blocks
    assert res.assert_ok == 1
    assert res.assert_fail == 0


def test_run_assume_false_stops() -> None:
    tac = parse_string(ASSUME_FAIL_TAC, path="<string>")
    res = run_program(tac.program, config=RunConfig())
    assert res.status == "stopped"
    assert "assume failed" in res.reason
    assert res.assert_ok == 0
    assert res.assert_fail == 0


def test_run_assert_fail_does_not_stop() -> None:
    tac = parse_string(RUN_TAC, path="<string>")
    # Force branch to "fail" by entering there directly with B1=false so
    # the assert in that block deterministically fails.
    res = run_program(
        tac.program,
        config=RunConfig(entry_block="fail", initial_store={"B1": Value("bool", False)}),
    )
    assert res.assert_fail == 1
    # assert failure itself does not stop; this run later stops on end-block assume.
    assert res.steps >= 2


def test_run_symbol_suffix_reads_use_same_register() -> None:
    tac = parse_string(SUFFIX_REF_TAC, path="<string>")
    res = run_program(tac.program, config=RunConfig())
    assert res.status == "done"
    assert int(res.final_store["R2"].data) == 0x27


def test_run_symbol_suffix_reads_can_be_kept_distinct() -> None:
    tac = parse_string(SUFFIX_REF_TAC, path="<string>")
    # With suffix-keeping, ``R1:5`` is a distinct symbol from ``R1``;
    # seed it so the read resolves and the assume can fail concretely.
    res = run_program(
        tac.program,
        config=RunConfig(
            strip_var_suffixes=False,
            initial_store={"R1:5": Value("bv", 0x10)},
        ),
    )
    assert res.status == "stopped"
    assert "assume failed" in res.reason


def test_run_snippet_print_events() -> None:
    tac = parse_string(PRINT_SNIPPET_TAC, path="<string>")
    res = run_program(tac.program, config=RunConfig())
    rendered = [e.rendered for e in res.events]
    assert "pre" in rendered
    x_event = next(e for e in res.events if e.rendered.strip() == "x")
    assert int(x_event.value.data) == 2  # type: ignore[union-attr]
    y_event = next(e for e in res.events if e.rendered.strip() == "y")
    assert int(y_event.value.data) == ((3 << 64) | 2)  # type: ignore[union-attr]
    tag_event = next(e for e in res.events if e.rendered.strip() == "x <= y")
    assert tag_event.value is None


def test_run_snippet_weak_use_dangling_does_not_materialize_store() -> None:
    tac = parse_string(PRINT_SNIPPET_DANGLING_TAC, path="<string>")
    res = run_program(tac.program, config=RunConfig())
    missing_event = next(e for e in res.events if e.rendered.strip() == "missing")
    assert missing_event.note == "dangling weak use: R9"
    assert "R9" not in res.final_store
