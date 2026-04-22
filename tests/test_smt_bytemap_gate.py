"""Tests for the ``ctac smt`` bytemap gate.

The gate rejects any input that isn't ``BYTEMAP_FREE``. This is the
interim behavior until ``sea_vc`` learns to encode bytemap ``Select``
reads, at which point the gate will relax to also accept
``BYTEMAP_RO``.
"""

from __future__ import annotations

from typer.testing import CliRunner

from ctac.tool.main import app


_BYTEMAP_RO_SRC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tB0:bool
\tM16:bytemap
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd M16
\t\tAssignExpCmd R0 Select(M16 0x10)
\t\tAssignHavocCmd R1
\t\tAssignExpCmd B0 Eq(R0 R1)
\t\tAssertCmd B0 "assertion failed"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


_BYTEMAP_FREE_SRC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tB0:bool
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignHavocCmd R1
\t\tAssignExpCmd B0 Eq(R0 R1)
\t\tAssertCmd B0 "assertion failed"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_smt_rejects_bytemap_ro_input(tmp_path):
    src = tmp_path / "ro.tac"
    src.write_text(_BYTEMAP_RO_SRC)
    runner = CliRunner()
    result = runner.invoke(app, ["smt", str(src), "--plain"])
    assert result.exit_code == 2, result.output
    assert "bytemap" in result.output.lower()
    assert "bytemap-ro" in result.output


def test_smt_accepts_bytemap_free_input(tmp_path):
    src = tmp_path / "free.tac"
    src.write_text(_BYTEMAP_FREE_SRC)
    runner = CliRunner()
    result = runner.invoke(app, ["smt", str(src), "--plain"])
    assert result.exit_code == 0, result.output
    # SMT-LIB output should be present.
    assert "(check-sat)" in result.output
