"""Parse-error type for Tiny TAC."""

from __future__ import annotations


class TtacParseError(Exception):
    """A lexing or parsing failure, carrying 1-based source position.

    ``line`` and ``col`` point at the offending token. When the source
    text is available, ``with_caret`` renders the offending line plus a
    caret under the column.
    """

    def __init__(self, message: str, line: int, col: int) -> None:
        self.message = message
        self.line = line
        self.col = col
        super().__init__(f"{line}:{col}: {message}")

    def with_caret(self, source: str) -> str:
        lines = source.splitlines()
        if 1 <= self.line <= len(lines):
            src_line = lines[self.line - 1]
            caret = " " * (self.col - 1) + "^"
            return f"{self}\n    {src_line}\n    {caret}"
        return str(self)


class VcGenError(Exception):
    """The program is not in proper form for VC generation, or uses a
    construct vcgen does not support (e.g. references, which must be
    desugared first)."""


class LeanGenError(Exception):
    """The program is outside the ttac-lean v1 fragment (scalar-only,
    pure SSA, loop-free, no use-before-def).

    Carries every violation so a single run reports all problems.
    """

    def __init__(self, errors: tuple[str, ...]) -> None:
        self.errors = errors
        super().__init__("lean generation failed:\n  " + "\n  ".join(errors))


class TtacTypeError(Exception):
    """Type inference could not produce a total typing.

    Carries every offender so a single run reports all problems: variables
    whose type stayed ``unknown``, variables with conflicting evidence, and
    expression-level type mismatches.
    """

    def __init__(
        self,
        *,
        unknown: tuple[str, ...] = (),
        conflicts: tuple[str, ...] = (),
        errors: tuple[str, ...] = (),
    ) -> None:
        self.unknown = unknown
        self.conflicts = conflicts
        self.errors = errors
        parts: list[str] = []
        if unknown:
            parts.append(f"untyped variables: {', '.join(unknown)}")
        if conflicts:
            parts.append(f"conflicting types: {', '.join(conflicts)}")
        if errors:
            parts.append("; ".join(errors))
        super().__init__("type inference failed: " + " | ".join(parts))
