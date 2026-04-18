from __future__ import annotations

from ctac.ir.models import TacBlock
from ctac.ast.nodes import JumpCmd, JumpiCmd
from ctac.tool.main import _pp_terminator_line


def test_pp_terminator_uses_jumpi_guard() -> None:
    block = TacBlock(
        id="B",
        successors=["T", "F"],
        commands=[
            JumpiCmd(
                raw="JumpiCmd T F B10:7",
                then_target="T",
                else_target="F",
                condition="B10:7",
            )
        ],
    )
    assert _pp_terminator_line(block, strip_var_suffixes=True) == "if B10 goto T else F"
    assert _pp_terminator_line(block, strip_var_suffixes=False) == "if B10:7 goto T else F"


def test_pp_terminator_uses_unconditional_jump() -> None:
    block = TacBlock(
        id="B",
        successors=["Z"],
        commands=[JumpCmd(raw="JumpCmd Z", target="Z")],
    )
    assert _pp_terminator_line(block, strip_var_suffixes=True) == "goto Z"

