from __future__ import annotations

from rich.highlighter import RegexHighlighter
from rich.text import Text
from rich.theme import Theme


class TacHighlighter(RegexHighlighter):
    """Syntax highlighter for TAC-like pretty-printed lines."""

    base_style = "ctac."
    highlights = [
        r"(?P<keyword>\b(?:assume|assert|goto|stop|havoc)\b)",
        r"(?P<control>\b(?:if|else)\b)",
        r"(?P<block>(?<=\bgoto\s)[A-Za-z0-9_]+)",
        r"(?P<block>(?<=,\s)[A-Za-z0-9_]+)",
        r"(?P<block>(?<=\belse\s)[A-Za-z0-9_]+)",
        r"(?P<function>\b[A-Za-z_][A-Za-z0-9_]*(?=\())",
        r"(?P<boolean>\b(?:true|false)\b)",
        r"(?P<number>\b0x[0-9a-fA-F_]+\b)",
        # Decimal numbers: plain digits, or 10k-grouped with 4-digit underscore chunks.
        r"(?P<number>\b(?:\d+|\d{1,4}(?:_\d{4})+)(?:\([A-Za-z0-9_]+\))?\b)",
        r"(?P<symbol>\b[RBIFTS][A-Za-z0-9_]*(?::\d+)?\b)",
        r"(?P<operator>==|<=|>=|<s|<=s|>s|>=s|&&|\|\||<<|>>s|>>|\+int|-int|\*int|/int|%int|[-+*/%&|^~!=<>])",
        r"(?P<comment>\s#.*$)",
        r"^(?P<label>[A-Za-z0-9_]+):\s*$",
    ]


TAC_THEME = Theme(
    {
        "ctac.label": "bold bright_green",
        "ctac.keyword": "bold bright_cyan",
        "ctac.control": "bold cyan",
        "ctac.block": "bold bright_green",
        "ctac.function": "bold bright_magenta",
        "ctac.boolean": "bold magenta",
        "ctac.number": "yellow",
        "ctac.symbol": "bright_blue",
        "ctac.operator": "bright_white",
        "ctac.comment": "dim",
    }
)

_TAC_HIGHLIGHTER = TacHighlighter()


def highlight_tac_line(line: str, *, base_style: str | None = None) -> Text:
    text = Text(line, style=base_style)
    _TAC_HIGHLIGHTER.highlight(text)
    return text
