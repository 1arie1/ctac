from __future__ import annotations

from rich.console import Console

from ctac.tool.stats_model import StatsCollection
from ctac.tool.stats_render import render_plain_stats, render_rich_stats_tree


def test_plain_stats_format_and_time_units() -> None:
    stats = StatsCollection()
    stats.add_num("overview.commands", 2345)
    stats.add_str("overview.path", "/tmp/in.tac")
    stats.add_time("timings.parse", 500, unit="ms")
    stats.add_time("timings.solve", 1500, unit="ms")
    stats.add_time("timings.optimize", 120_000, unit="ms")
    stats.add_time("timings.total", 7_200_000, unit="ms")

    lines = render_plain_stats(stats)
    assert lines == [
        "overview.commands: 2,345",
        "overview.path: /tmp/in.tac",
        "timings.parse: 500ms",
        "timings.solve: 1.5s",
        "timings.optimize: 2m",
        "timings.total: 2h",
    ]


def test_plain_stats_last_write_wins_but_order_stays_deterministic() -> None:
    stats = StatsCollection()
    stats.add_num("a.count", 1)
    stats.add_num("b.count", 2)
    stats.add_num("a.count", 9)

    lines = render_plain_stats(stats)
    assert lines == [
        "a.count: 9",
        "b.count: 2",
    ]


def test_rich_stats_tree_hierarchy_and_typed_colors() -> None:
    stats = StatsCollection()
    stats.add_num("solver.bv.add", 2345)
    stats.add_str("solver.mode", "qf_bv")
    stats.add_time("solver.elapsed", 1500, unit="ms")

    tree = render_rich_stats_tree(stats)
    section = tree.children[0]
    leaves = {child.label.plain.split(" ", 1)[0]: child.label for child in section.children if hasattr(child.label, "plain")}

    assert "mode" in leaves
    assert "elapsed" in leaves
    assert "bv" in {child.label.plain for child in section.children if hasattr(child.label, "plain")}

    elapsed_styles = [span.style for span in leaves["elapsed"].spans]
    mode_styles = [span.style for span in leaves["mode"].spans]
    assert "yellow" in elapsed_styles
    assert "magenta" in mode_styles

    console = Console(record=True, force_terminal=False, no_color=True)
    console.print(tree)
    txt = console.export_text()
    assert "solver" in txt
    assert "add" in txt
    assert "2,345" in txt
