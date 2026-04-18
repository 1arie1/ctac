"""Def/use extraction for TAC programs."""

from __future__ import annotations

from collections import defaultdict

from ctac.analysis.expr_walk import command_uses
from ctac.analysis.model import BlockDefUse, DefUseResult, DefinitionSite, UseSite
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import AssignExpCmd, AssignHavocCmd, JumpCmd, JumpiCmd
from ctac.ir.models import TacProgram


def _is_terminator_kind(cmd: object) -> bool:
    return isinstance(cmd, (JumpCmd, JumpiCmd))


def extract_def_use(program: TacProgram, *, strip_var_suffixes: bool = True) -> DefUseResult:
    by_block: dict[str, BlockDefUse] = {}
    defs_by_symbol: dict[str, list[DefinitionSite]] = defaultdict(list)
    uses_by_symbol: dict[str, list[UseSite]] = defaultdict(list)
    symbol_to_id: dict[str, int] = {}
    id_to_symbol: list[str] = []
    definitions: list[DefinitionSite] = []
    next_def_id = 0

    def _symbol_id(sym: str) -> int:
        if sym in symbol_to_id:
            return symbol_to_id[sym]
        sid = len(id_to_symbol)
        symbol_to_id[sym] = sid
        id_to_symbol.append(sym)
        return sid

    for block in program.blocks:
        defs_in_block: list[str] = []
        uses_in_block: list[str] = []
        kills_in_block: set[str] = set()
        definition_sites: list[DefinitionSite] = []
        use_sites: list[UseSite] = []

        seen_static = False
        seen_dynamic = False
        seen_terminator = False
        dsa_shape_ok = True
        dsa_shape_violation: str | None = None

        for idx, cmd in enumerate(block.commands):
            cmd_kind = type(cmd).__name__

            for sym in command_uses(cmd, strip_var_suffixes=strip_var_suffixes):
                sid = _symbol_id(sym)
                us = UseSite(
                    symbol_id=sid,
                    symbol=sym,
                    block_id=block.id,
                    cmd_index=idx,
                    cmd_kind=cmd_kind,
                    raw=cmd.raw,
                )
                use_sites.append(us)
                uses_by_symbol[sym].append(us)
                if sym not in uses_in_block:
                    uses_in_block.append(sym)

            if isinstance(cmd, AssignExpCmd):
                seen_static = True
                if seen_dynamic and dsa_shape_ok:
                    dsa_shape_ok = False
                    dsa_shape_violation = "static assignment appears after dynamic assignment"
                if seen_terminator and dsa_shape_ok:
                    dsa_shape_ok = False
                    dsa_shape_violation = "assignment appears after terminator"
                lhs = canonical_symbol(cmd.lhs, strip_var_suffixes=strip_var_suffixes)
                sid = _symbol_id(lhs)
                ds = DefinitionSite(
                    def_id=next_def_id,
                    origin_uid=f"def:{next_def_id}",
                    symbol_id=sid,
                    symbol=lhs,
                    block_id=block.id,
                    cmd_index=idx,
                    cmd_kind=cmd_kind,
                    raw=cmd.raw,
                )
                next_def_id += 1
                definition_sites.append(ds)
                defs_by_symbol[lhs].append(ds)
                definitions.append(ds)
                if lhs not in defs_in_block:
                    defs_in_block.append(lhs)
                kills_in_block.add(lhs)
            elif isinstance(cmd, AssignHavocCmd):
                # Havoc is environment/model initialization in many TACs (especially entry blocks),
                # not a DSA "dynamic assignment" in the sense of late-block dynamic updates.
                # Treat havoc as a regular assignment for shape checks.
                seen_static = True
                if seen_terminator and dsa_shape_ok:
                    dsa_shape_ok = False
                    dsa_shape_violation = "assignment appears after terminator"
                lhs = canonical_symbol(cmd.lhs, strip_var_suffixes=strip_var_suffixes)
                sid = _symbol_id(lhs)
                ds = DefinitionSite(
                    def_id=next_def_id,
                    origin_uid=f"def:{next_def_id}",
                    symbol_id=sid,
                    symbol=lhs,
                    block_id=block.id,
                    cmd_index=idx,
                    cmd_kind=cmd_kind,
                    raw=cmd.raw,
                )
                next_def_id += 1
                definition_sites.append(ds)
                defs_by_symbol[lhs].append(ds)
                definitions.append(ds)
                if lhs not in defs_in_block:
                    defs_in_block.append(lhs)
                kills_in_block.add(lhs)
            elif _is_terminator_kind(cmd):
                seen_terminator = True
            else:
                if seen_terminator and dsa_shape_ok:
                    dsa_shape_ok = False
                    dsa_shape_violation = f"non-terminator command {cmd_kind} appears after terminator"

        by_block[block.id] = BlockDefUse(
            block_id=block.id,
            defs=tuple(defs_in_block),
            uses=tuple(uses_in_block),
            kills=tuple(sorted(kills_in_block)),
            definition_sites=tuple(definition_sites),
            use_sites=tuple(use_sites),
            dsa_shape_ok=dsa_shape_ok,
            dsa_shape_violation=dsa_shape_violation,
        )

    defs_out = {k: tuple(v) for k, v in defs_by_symbol.items()}
    uses_out = {k: tuple(v) for k, v in uses_by_symbol.items()}
    return DefUseResult(
        by_block=by_block,
        definitions_by_symbol=defs_out,
        uses_by_symbol=uses_out,
        symbol_to_id=symbol_to_id,
        id_to_symbol=tuple(id_to_symbol),
        definitions=tuple(definitions),
    )
