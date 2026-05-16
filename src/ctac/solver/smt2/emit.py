"""Emit an `Smt2File` back to source.

Per-statement policy:
- `dirty=False` AND has a valid source span: emit `src[span[0]:span[1]]`
  verbatim. This is byte-identical for unchanged statements.
- `dirty=True` OR no span (newly constructed): re-render via the
  pretty-printer (`pp.py`) at the policy width.

Whitespace between statements: we preserve it by slicing from the END of
one statement's span to the START of the next. This captures blank
lines and any leading whitespace before the first form.
"""
from __future__ import annotations

from ctac.solver.smt2.parser import Smt2File


def emit(file: Smt2File) -> str:
    """Render `file` back to a source string.

    Round-trip guarantee: if no statement has `dirty=True`, the result
    is byte-identical to `file.source`."""
    if not file.statements:
        return file.source
    from ctac.solver.smt2.pp import pp_statement, PpPolicy
    from ctac.solver.smt2.doc import render

    policy = PpPolicy()
    src = file.source
    parts: list[str] = []

    # Leading whitespace before the first statement, only if we have a source
    # AND the first statement has a valid span.
    first = file.statements[0]
    if src and first.span[0] >= 0 and first.span[0] > 0:
        parts.append(src[:first.span[0]])

    for i, stmt in enumerate(file.statements):
        if stmt.dirty or stmt.span == (-1, -1) or not src:
            parts.append(render(pp_statement(stmt, policy), width=policy.width))
        else:
            parts.append(src[stmt.span[0]:stmt.span[1]])
        # Inter-statement whitespace
        if i + 1 < len(file.statements):
            nxt = file.statements[i + 1]
            if (stmt.span[1] >= 0 and nxt.span[0] >= 0 and
                src and stmt.span[1] <= nxt.span[0]):
                parts.append(src[stmt.span[1]:nxt.span[0]])
            else:
                # Inserted or moved statement — just put a single newline
                parts.append('\n')

    # Trailing whitespace after the last statement
    last = file.statements[-1]
    if src and last.span[1] >= 0 and last.span[1] < len(src):
        parts.append(src[last.span[1]:])
    elif not parts[-1].endswith('\n'):
        parts.append('\n')

    return ''.join(parts)
