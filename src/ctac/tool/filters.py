"""Shared CFG filter options for ``cfg``, ``pp``, and future commands."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from ctac.ast.models import TacProgram
from ctac.graph import Cfg, CfgFilter


@dataclass
class CfgFilterOptions:
    """Same flags as ``ctac cfg`` / ``ctac pp``; combined with AND (intersection)."""

    to_block: Optional[str] = None
    from_block: Optional[str] = None
    only: Optional[str] = None
    id_contains: Optional[str] = None
    id_regex: Optional[str] = None
    cmd_contains: Optional[str] = None
    exclude: Optional[str] = None

    def any_active(self) -> bool:
        return any(
            (
                self.to_block,
                self.from_block,
                self.only,
                self.id_contains,
                self.id_regex,
                self.cmd_contains,
                self.exclude,
            )
        )


def apply_cfg_filters(program: TacProgram, opt: CfgFilterOptions) -> tuple[TacProgram, list[str]]:
    """Return filtered program and warning lines (empty if no filters)."""
    if not opt.any_active():
        return program, []
    filtered, warnings = Cfg(program).filtered(
        CfgFilter(
            to_id=opt.to_block,
            from_id=opt.from_block,
            only_ids=Cfg.parse_csv_ids(opt.only),
            id_contains=opt.id_contains,
            id_regex=opt.id_regex,
            cmd_contains=opt.cmd_contains,
            exclude_ids=Cfg.parse_csv_ids(opt.exclude),
        )
    )
    return filtered.program, warnings
