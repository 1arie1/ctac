from __future__ import annotations

from dataclasses import dataclass, field

from rich.text import Text
from rich.tree import Tree

from ctac.tool.stats_model import StatEntry, StatType, StatValue, StatsCollection


def _fmt_num(value: int | float) -> str:
    if isinstance(value, int):
        return f"{value:,}"
    if float(value).is_integer():
        return f"{int(value):,}"
    s = f"{value:,.3f}"
    return s.rstrip("0").rstrip(".")


def _fmt_time_ms(ms_value: float) -> str:
    ms = float(ms_value)
    if ms >= 3_600_000:
        return f"{_fmt_float(ms / 3_600_000)}h"
    if ms >= 60_000:
        return f"{_fmt_float(ms / 60_000)}m"
    if ms >= 1_000:
        return f"{_fmt_float(ms / 1_000)}s"
    return f"{_fmt_float(ms)}ms"


def _fmt_float(v: float) -> str:
    if float(v).is_integer():
        return f"{int(v):,}"
    s = f"{v:,.3f}"
    return s.rstrip("0").rstrip(".")


def format_stat_value(value: StatValue) -> str:
    if value.kind is StatType.NUM:
        return _fmt_num(value.value if isinstance(value.value, (int, float)) else 0)
    if value.kind is StatType.TIME:
        return _fmt_time_ms(float(value.value))
    return str(value.value)


def render_plain_stats(stats: StatsCollection) -> list[str]:
    return [f"{ent.path}: {format_stat_value(ent.value)}" for ent in stats.entries()]


@dataclass
class _TrieNode:
    children: dict[str, _TrieNode] = field(default_factory=dict)
    value: StatValue | None = None


def render_rich_stats_tree(stats: StatsCollection, *, root_label: str = "stats") -> Tree:
    trie = _TrieNode()
    for ent in stats.entries():
        _insert_entry(trie, ent)

    root = Tree(Text(root_label, style="magenta"), guide_style="bright_black")
    _render_children(trie, root)
    return root


def _insert_entry(root: _TrieNode, entry: StatEntry) -> None:
    cur = root
    for seg in entry.path.split("."):
        cur = cur.children.setdefault(seg, _TrieNode())
    cur.value = entry.value


def _render_children(node: _TrieNode, out: Tree) -> None:
    for seg, child in node.children.items():
        if child.children:
            label = Text(seg, style="blue")
            child_tree = out.add(label)
            if child.value is not None:
                child_tree.add(_render_leaf_line("value", child.value))
            _render_children(child, child_tree)
            continue

        if child.value is None:
            continue
        out.add(_render_leaf_line(seg, child.value))


def _render_leaf_line(label: str, value: StatValue) -> Text:
    val_s = format_stat_value(value)
    dots = "." * max(6, 44 - len(label) - len(val_s))
    t = Text()
    t.append(label, style="cyan")
    t.append(" ")
    t.append(dots, style="dim")
    t.append(" ")
    if value.kind is StatType.NUM:
        t.append(val_s, style="green")
    elif value.kind is StatType.TIME:
        t.append(val_s, style="yellow")
    else:
        t.append(val_s, style="magenta")
    return t
