from __future__ import annotations

import pytest

from ctac.graph import filtered_program, resolve_cfg_keep_ids
from ctac.parse import parse_string

from test_parse_minimal import MINIMAL_TAC


@pytest.fixture
def minimal():
    return parse_string(MINIMAL_TAC, path="<string>")


def test_only_allowlist_and_unknown_warning(minimal):
    keep, warns = resolve_cfg_keep_ids(
        minimal.program,
        only_ids=frozenset(["entry", "ghost", "nope"]),
    )
    assert keep == {"entry"}
    assert len(warns) == 1
    assert "ghost" in warns[0] or "nope" in warns[0]


def test_to_ancestors(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, to_id="exit")
    assert keep == {"entry", "loop", "exit"}


def test_from_descendants(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, from_id="loop")
    assert keep == {"loop", "entry", "exit"}


def test_between_entry_and_loop(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, from_id="entry", to_id="loop")
    assert keep == {"entry", "loop"}


def test_between_entry_and_exit(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, from_id="entry", to_id="exit")
    assert keep == {"entry", "loop", "exit"}


def test_id_contains_and_exclude(minimal):
    keep, _ = resolve_cfg_keep_ids(
        minimal.program,
        to_id="exit",
        id_contains="oo",
        exclude_ids=frozenset(["entry"]),
    )
    assert keep == {"loop"}


def test_id_contains_only(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, id_contains="oo")
    assert keep == {"loop"}


def test_cmd_contains(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, cmd_contains="AssignExpCmd x 0x2")
    assert keep == {"loop"}


def test_id_regex_invalid(minimal):
    with pytest.raises(ValueError, match="id-regex"):
        resolve_cfg_keep_ids(minimal.program, id_regex="[")


def test_id_regex_ok(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, id_regex=r"^lo")
    assert keep == {"loop"}


def test_filtered_induces_edges(minimal):
    keep, _ = resolve_cfg_keep_ids(minimal.program, only_ids=frozenset(["entry", "exit"]))
    sub = filtered_program(minimal.program, keep)
    by = sub.block_by_id()
    assert by["entry"].successors == ["exit"]
    assert by["exit"].successors == []


def test_filtered_preserves_successors_for_renderers(minimal):
    """``Cfg.filtered(preserve_successors=True)`` keeps each kept
    block's original successor list verbatim — even when the
    successor isn't in the slice. Used by ``pp`` / ``cfg`` so the
    rendered terminator reflects the real CFG instead of being
    silently rewritten to ``stop``."""
    from ctac.graph import Cfg, CfgFilter

    sub_cfg, _ = Cfg(minimal.program).filtered(
        CfgFilter(only_ids=frozenset(["entry"])),
        preserve_successors=True,
    )
    by = sub_cfg.program.block_by_id()
    assert by["entry"].successors == ["exit", "loop"]


def test_unknown_to_raises(minimal):
    with pytest.raises(ValueError, match="unknown block"):
        resolve_cfg_keep_ids(minimal.program, to_id="missing")
