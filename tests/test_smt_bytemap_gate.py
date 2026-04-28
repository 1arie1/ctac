"""Tests for the ``ctac smt`` bytemap gate.

The gate accepts ``BYTEMAP_FREE`` and ``BYTEMAP_RO`` and rejects
``BYTEMAP_RW``. Store-based updates are the remaining unsupported
case; lifting that gate is future work.
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


_BYTEMAP_RW_SRC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tM16:bytemap
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd M16
\t\tAssignExpCmd M16 Store(M16 0x10 0x42)
\t\tAssignExpCmd R0 Select(M16 0x10)
\t\tAssertCmd false "assertion failed"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_smt_accepts_bytemap_ro_input(tmp_path):
    src = tmp_path / "ro.tac"
    src.write_text(_BYTEMAP_RO_SRC)
    runner = CliRunner()
    result = runner.invoke(app, ["smt", str(src), "--plain"])
    assert result.exit_code == 0, result.output
    # SMT-LIB output should be present; memory symbol declared as a UF.
    assert "(check-sat)" in result.output
    assert "(declare-fun M16 (Int) Int)" in result.output


def test_smt_accepts_bytemap_free_input(tmp_path):
    src = tmp_path / "free.tac"
    src.write_text(_BYTEMAP_FREE_SRC)
    runner = CliRunner()
    result = runner.invoke(app, ["smt", str(src), "--plain"])
    assert result.exit_code == 0, result.output
    # SMT-LIB output should be present.
    assert "(check-sat)" in result.output


def test_smt_accepts_bytemap_rw_input(tmp_path):
    """sea_vc encodes bytemap-rw via lambda-style ``define-fun`` per
    map. ``Store(M, k, v)`` becomes a function body
    ``(ite (= i k) v (M i))``; ``Select`` is unchanged. Used to be
    rejected at the precondition; now succeeds."""
    src = tmp_path / "rw.tac"
    src.write_text(_BYTEMAP_RW_SRC)
    runner = CliRunner()
    result = runner.invoke(app, ["smt", str(src), "--plain"])
    assert result.exit_code == 0, result.output
    assert "(check-sat)" in result.output
    # Map definitions are hoisted to the top under their banner.
    assert "Bytemap Definitions (lambda form)" in result.output
    # The Store body emits the canonical ITE shape.
    assert "(ite (= i_map" in result.output
