"""Syntax highlighting for pretty-printed Tiny TAC (used by ``ttac pp``).

A Rich ``RegexHighlighter`` over the ``ttac`` surface syntax: keywords,
control words, type names, booleans, block-label targets, numbers, and
operators. Mirrors the role of ``ctac.ast.highlight`` but for ttac's
keyword set and infix grammar.
"""

from __future__ import annotations

from rich.highlighter import RegexHighlighter
from rich.text import Text
from rich.theme import Theme


class TtacHighlighter(RegexHighlighter):
    base_style = "ttac."
    highlights = [
        r"(?P<keyword>\b(?:assume|assert|havoc|halt|goto|phi|borrow_mut|"
        r"borrow_ref_mut|borrow_ref|borrow|get_ref|put_ref|release|not|and|or)\b)",
        r"(?P<control>\b(?:if|else)\b)",
        r"(?P<type>\b(?:bool|int|bytemap|ref)\b)",
        r"(?P<boolean>\b(?:true|false)\b)",
        # Block-label targets in terminators, and `label:` block headers.
        r"(?P<block>(?<=\bgoto\s)[A-Za-z_][A-Za-z0-9_]*)",
        r"(?P<block>(?<=\belse\s)[A-Za-z_][A-Za-z0-9_]*)",
        r"^(?P<label>[A-Za-z_][A-Za-z0-9_]*)(?=:)",
        r"(?P<number>\b\d+\b)",
        r"(?P<operator>:=|==|<=|<|\+|-|\*|/)",
        r"(?P<comment>//.*$)",
    ]


TTAC_THEME = Theme(
    {
        "ttac.label": "bold bright_green",
        "ttac.keyword": "bold bright_cyan",
        "ttac.control": "bold cyan",
        "ttac.type": "bold blue",
        "ttac.boolean": "bold magenta",
        "ttac.block": "bold bright_green",
        "ttac.number": "yellow",
        "ttac.operator": "bright_white",
        "ttac.comment": "dim",
    }
)

_HIGHLIGHTER = TtacHighlighter()


def highlight_line(line: str) -> Text:
    text = Text(line)
    _HIGHLIGHTER.highlight(text)
    return text
