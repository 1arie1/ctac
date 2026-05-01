"""``--narrow-range`` opt-in: in-range axiom for narrow assignments."""

from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.parse import parse_string
from ctac.smt import build_vc, render_smt_script
from ctac.tool.main import app


_TAC_NARROW = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t\tsafe_math_narrow_bv256:JSON{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow.Implicit","returnSort":{"bits":256}}
\t}
\tUninterpretedFunctions {
\t}
\tR1017:bv256
\tR1019:bv256
\tflag:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd R1017
\t\tAssumeExpCmd LAnd(Ge(R1017 0x0) Le(R1017 0x10))
\t\tAssignExpCmd R1019 Apply(safe_math_narrow_bv256:bif IntAdd(0x1(int) R1017))
\t\tAssignExpCmd flag Le(R1019 0x100)
\t\tAssertCmd flag "in-range"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_narrow_range_off_by_default() -> None:
    """Without ``--narrow-range`` the encoder leaves R1019 unconstrained
    beyond its sort. The historical pre-axiom shape is preserved."""
    tac = parse_string(_TAC_NARROW)
    script = build_vc(tac)
    text = render_smt_script(script)
    # The narrow assignment's equality is present.
    assert "R1019" in text
    # No range axiom on R1019 is emitted (the only `(<= 0 R1019` would
    # come from the new code path).
    assert "(<= 0 R1019" not in text


def test_narrow_range_emits_lhs_axiom() -> None:
    """With ``--narrow-range`` the LHS of every static
    ``Apply(safe_math_narrow_bvN:bif, ...)`` assignment gets
    ``(<= 0 lhs BV256_MAX)`` added."""
    tac = parse_string(_TAC_NARROW)
    script = build_vc(tac, narrow_range=True)
    text = render_smt_script(script)
    assert "(<= 0 R1019 BV256_MAX)" in text


def test_narrow_range_skips_non_narrow_assignment() -> None:
    """An assignment whose RHS is plain (no narrow) is unaffected even
    when ``--narrow-range`` is on. ``flag`` is bool here so there is no
    bv256 axiom for it; ``R1017`` is a havoc and gets the existing
    havoc-range axiom (handled by the unrelated path)."""
    tac = parse_string(_TAC_NARROW)
    script = build_vc(tac, narrow_range=True)
    text = render_smt_script(script)
    # No narrow-derived axiom for `flag` (it's a Bool, not bv256, and
    # its RHS is `Le(...)`, not narrow).
    assert "(<= 0 flag" not in text


def test_narrow_range_cli_flag(tmp_path: Path) -> None:
    """``ctac smt --narrow-range`` propagates through the CLI."""
    f = tmp_path / "narrow.tac"
    f.write_text(_TAC_NARROW, encoding="utf-8")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(f), "--plain", "--narrow-range"])
    assert res.exit_code == 0, res.output
    assert "(<= 0 R1019 BV256_MAX)" in res.output


def test_narrow_range_cli_default_omits_axiom(tmp_path: Path) -> None:
    """Without the flag, the CLI keeps the historical encoding."""
    f = tmp_path / "narrow_default.tac"
    f.write_text(_TAC_NARROW, encoding="utf-8")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(f), "--plain"])
    assert res.exit_code == 0, res.output
    assert "(<= 0 R1019" not in res.output


_TAC_NARROW_NESTED = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t\tsafe_math_narrow_bv256:JSON{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow.Implicit","returnSort":{"bits":256}}
\t}
\tUninterpretedFunctions {
\t}
\tR1:bv256
\tR2:bv256
\tflag:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd R1
\t\tAssumeExpCmd LAnd(Ge(R1 0x0) Le(R1 0x10))
\t\tAssignExpCmd R2 Apply(safe_math_narrow_bv256:bif IntAdd(0x50(int) Apply(safe_math_narrow_bv256:bif IntAdd(0x2800(int) R1))))
\t\tAssignExpCmd flag Le(R2 0xffffffff)
\t\tAssertCmd flag "nested narrow"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_narrow_range_axiom_for_outermost_narrow() -> None:
    """When the RHS is a top-level narrow whose inner expression itself
    contains another narrow, the LHS still gets exactly one axiom (the
    inner narrow has no named LHS to attach to)."""
    tac = parse_string(_TAC_NARROW_NESTED)
    script = build_vc(tac, narrow_range=True)
    text = render_smt_script(script)
    assert text.count("(<= 0 R2 BV256_MAX)") == 1
