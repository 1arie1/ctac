"""Serialize ``TacCmd`` / ``TacExpr`` back into canonical TAC command text.

The parser (``ctac.ast.parse_cmd``) is tolerant of whitespace, so the unparser
emits one canonical form (``Op(arg1 arg2 ...)``, no trailing space before the
closing paren). The output is guaranteed parseable — :func:`canonicalize_cmd`
composes with ``parse_command_line`` to round-trip any supported command.
"""

from __future__ import annotations

from dataclasses import replace

from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)


def unparse_expr(expr: TacExpr) -> str:
    """Render a ``TacExpr`` to its canonical TAC dump string."""
    if isinstance(expr, ConstExpr):
        return expr.value
    if isinstance(expr, SymbolRef):
        return expr.name
    if isinstance(expr, ApplyExpr):
        if not expr.args:
            return f"{expr.op}()"
        return f"{expr.op}({' '.join(unparse_expr(a) for a in expr.args)})"
    raise TypeError(f"cannot unparse expression: {expr!r}")


def _head(base: str, meta_index: int | None) -> str:
    return f"{base}:{meta_index}" if meta_index is not None else base


def unparse_cmd(cmd: TacCmd) -> str:
    """Render a ``TacCmd`` to its canonical TAC dump string."""
    if isinstance(cmd, AssignExpCmd):
        return f"{_head('AssignExpCmd', cmd.meta_index)} {cmd.lhs} {unparse_expr(cmd.rhs)}"
    if isinstance(cmd, AssumeExpCmd):
        return f"{_head('AssumeExpCmd', cmd.meta_index)} {unparse_expr(cmd.condition)}"
    if isinstance(cmd, AssignHavocCmd):
        return f"{_head('AssignHavocCmd', cmd.meta_index)} {cmd.lhs}"
    if isinstance(cmd, AnnotationCmd):
        # AnnotationCmd payload is opaque JSON-ish text; preserve raw when possible.
        return f"{_head('AnnotationCmd', cmd.meta_index)} {cmd.payload}"
    if isinstance(cmd, LabelCmd):
        # Stored text is the unquoted body; the parser expects quotes.
        return f'{_head("LabelCmd", cmd.meta_index)} "{cmd.text}"'
    if isinstance(cmd, JumpCmd):
        return f"{_head('JumpCmd', cmd.meta_index)} {cmd.target}"
    if isinstance(cmd, JumpiCmd):
        return (
            f"{_head('JumpiCmd', cmd.meta_index)} "
            f"{cmd.then_target} {cmd.else_target} {cmd.condition}"
        )
    if isinstance(cmd, AssertCmd):
        pred_text = unparse_expr(cmd.predicate)
        if cmd.message is None:
            return f"{_head('AssertCmd', cmd.meta_index)} {pred_text}"
        return f'{_head("AssertCmd", cmd.meta_index)} {pred_text} "{cmd.message}"'
    if isinstance(cmd, RawCmd):
        return cmd.raw
    raise TypeError(f"cannot unparse command: {cmd!r}")


def canonicalize_cmd(cmd: TacCmd) -> TacCmd:
    """Return ``cmd`` with its ``raw`` field rewritten from the AST.

    Used after a rewrite mutates the AST so ``render_program`` emits the new
    shape.  If the freshly-unparsed text already matches ``cmd.raw.strip()``
    the original command is returned unchanged (avoids extra allocations and
    preserves whitespace quirks of the parsed input for untouched commands).
    """
    new_raw = unparse_cmd(cmd)
    if new_raw == cmd.raw.strip():
        return cmd
    return replace(cmd, raw=new_raw)
