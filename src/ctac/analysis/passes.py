"""Concrete TAC data-flow analyses and transforms."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import replace

from ctac.analysis.defuse import extract_def_use
from ctac.analysis.framework import run_backward, run_forward
from ctac.analysis.model import (
    ControlDependenceResult,
    DceResult,
    DeadAssignment,
    DefUseResult,
    DefinitionSite,
    DsaDynamicAssignment,
    DsaIssue,
    DsaResult,
    LivenessResult,
    ProgramPoint,
    ReachingDefinitionsResult,
    UseBeforeDefIssue,
    UseBeforeDefResult,
)
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import AssignExpCmd, AssignHavocCmd
from ctac.graph import Cfg
from ctac.ir.models import TacBlock, TacProgram

RDStateFast = dict[int, int]  # symbol_id -> bitset(def_id)


def _rd_join_fast(states: list[RDStateFast]) -> RDStateFast:
    out: RDStateFast = {}
    for st in states:
        for sid, mask in st.items():
            out[sid] = out.get(sid, 0) | mask
    return out


def _rd_equals_fast(a: RDStateFast, b: RDStateFast) -> bool:
    return a == b


def _bit_defs(mask: int, definitions: tuple[DefinitionSite, ...]) -> tuple[DefinitionSite, ...]:
    out: list[DefinitionSite] = []
    m = mask
    while m:
        lsb = m & -m
        did = lsb.bit_length() - 1
        if 0 <= did < len(definitions):
            out.append(definitions[did])
        m ^= lsb
    return tuple(out)


def _freeze_rd_state_fast(
    st: RDStateFast,
    *,
    id_to_symbol: tuple[str, ...],
    definitions: tuple[DefinitionSite, ...],
) -> dict[str, tuple[DefinitionSite, ...]]:
    out: dict[str, tuple[DefinitionSite, ...]] = {}
    for sid, mask in st.items():
        if sid >= len(id_to_symbol):
            continue
        out[id_to_symbol[sid]] = _bit_defs(mask, definitions)
    return out


def _compute_reaching_block_states(
    program: TacProgram,
    *,
    du: DefUseResult,
) -> tuple[dict[str, RDStateFast], dict[str, RDStateFast]]:
    def _transfer_block_fast(block_id: str, in_state: RDStateFast) -> RDStateFast:
        cur: RDStateFast = dict(in_state)
        for ds in du.by_block[block_id].definition_sites:
            cur[ds.symbol_id] = 1 << ds.def_id
        return cur

    return run_forward(
        program,
        bottom={},
        join=_rd_join_fast,
        transfer=_transfer_block_fast,
        equals=_rd_equals_fast,
    )


def analyze_reaching_definitions(
    program: TacProgram,
    *,
    strip_var_suffixes: bool = True,
    def_use: DefUseResult | None = None,
) -> ReachingDefinitionsResult:
    du = def_use if def_use is not None else extract_def_use(program, strip_var_suffixes=strip_var_suffixes)
    by_id = program.block_by_id()
    block_in_fast, block_out_fast = _compute_reaching_block_states(program, du=du)

    in_by_cmd: dict[ProgramPoint, dict[str, tuple[DefinitionSite, ...]]] = {}
    out_by_cmd: dict[ProgramPoint, dict[str, tuple[DefinitionSite, ...]]] = {}
    for bid, block in by_id.items():
        state: RDStateFast = dict(block_in_fast.get(bid, {}))
        defs_by_idx: dict[int, list[DefinitionSite]] = defaultdict(list)
        for ds in du.by_block[bid].definition_sites:
            defs_by_idx[ds.cmd_index].append(ds)
        for idx, _cmd in enumerate(block.commands):
            pt = ProgramPoint(bid, idx)
            in_by_cmd[pt] = _freeze_rd_state_fast(
                state,
                id_to_symbol=du.id_to_symbol,
                definitions=du.definitions,
            )
            for ds in defs_by_idx.get(idx, []):
                state[ds.symbol_id] = 1 << ds.def_id
            out_by_cmd[pt] = _freeze_rd_state_fast(
                state,
                id_to_symbol=du.id_to_symbol,
                definitions=du.definitions,
            )

    return ReachingDefinitionsResult(
        in_by_block={
            bid: _freeze_rd_state_fast(st, id_to_symbol=du.id_to_symbol, definitions=du.definitions)
            for bid, st in block_in_fast.items()
        },
        out_by_block={
            bid: _freeze_rd_state_fast(st, id_to_symbol=du.id_to_symbol, definitions=du.definitions)
            for bid, st in block_out_fast.items()
        },
        in_by_command=in_by_cmd,
        out_by_command=out_by_cmd,
    )


def analyze_use_before_def(
    program: TacProgram,
    *,
    strip_var_suffixes: bool = True,
    def_use: DefUseResult | None = None,
    reaching_defs: ReachingDefinitionsResult | None = None,
) -> UseBeforeDefResult:
    du = def_use if def_use is not None else extract_def_use(program, strip_var_suffixes=strip_var_suffixes)
    issues: list[UseBeforeDefIssue] = []
    if reaching_defs is not None:
        rd = reaching_defs
        for block in program.blocks:
            uses_by_idx: dict[int, list] = defaultdict(list)
            for us in du.by_block[block.id].use_sites:
                uses_by_idx[us.cmd_index].append(us)
            for idx, _cmd in enumerate(block.commands):
                pt = ProgramPoint(block.id, idx)
                before = rd.in_by_command.get(pt, {})
                for us in uses_by_idx.get(idx, []):
                    if not before.get(us.symbol):
                        issues.append(
                            UseBeforeDefIssue(
                                symbol=us.symbol,
                                block_id=us.block_id,
                                cmd_index=us.cmd_index,
                                cmd_kind=us.cmd_kind,
                                raw=us.raw,
                            )
                        )
        return UseBeforeDefResult(issues=tuple(issues))

    block_in_fast, _ = _compute_reaching_block_states(program, du=du)
    for block in program.blocks:
        state: RDStateFast = dict(block_in_fast.get(block.id, {}))
        uses_by_idx: dict[int, list] = defaultdict(list)
        defs_by_idx: dict[int, list[DefinitionSite]] = defaultdict(list)
        for ds in du.by_block[block.id].definition_sites:
            defs_by_idx[ds.cmd_index].append(ds)
        for us in du.by_block[block.id].use_sites:
            uses_by_idx[us.cmd_index].append(us)
        for idx, _cmd in enumerate(block.commands):
            for us in uses_by_idx.get(idx, []):
                if state.get(us.symbol_id, 0) == 0:
                    issues.append(
                        UseBeforeDefIssue(
                            symbol=us.symbol,
                            block_id=us.block_id,
                            cmd_index=us.cmd_index,
                            cmd_kind=us.cmd_kind,
                            raw=us.raw,
                        )
                    )
            for ds in defs_by_idx.get(idx, []):
                state[ds.symbol_id] = 1 << ds.def_id
    return UseBeforeDefResult(issues=tuple(issues))


def _liveness_transfer_for_block(du: DefUseResult, block_id: str, out_state: frozenset[str]) -> frozenset[str]:
    live = set(out_state)
    block = du.by_block[block_id]
    defs_by_idx: dict[int, list[str]] = defaultdict(list)
    uses_by_idx: dict[int, list[str]] = defaultdict(list)
    for ds in block.definition_sites:
        defs_by_idx[ds.cmd_index].append(ds.symbol)
    for us in block.use_sites:
        uses_by_idx[us.cmd_index].append(us.symbol)

    max_idx = -1
    if block.definition_sites:
        max_idx = max(max_idx, max(ds.cmd_index for ds in block.definition_sites))
    if block.use_sites:
        max_idx = max(max_idx, max(us.cmd_index for us in block.use_sites))
    for idx in range(max_idx, -1, -1):
        for sym in defs_by_idx.get(idx, []):
            live.discard(sym)
        for sym in uses_by_idx.get(idx, []):
            live.add(sym)
    return frozenset(sorted(live))


def analyze_liveness(
    program: TacProgram,
    *,
    strip_var_suffixes: bool = True,
    def_use: DefUseResult | None = None,
) -> LivenessResult:
    du = def_use if def_use is not None else extract_def_use(program, strip_var_suffixes=strip_var_suffixes)

    block_in, block_out = run_backward(
        program,
        bottom=frozenset(),
        join=lambda states: frozenset(sorted(set().union(*states))) if states else frozenset(),
        transfer=lambda bid, out_st: _liveness_transfer_for_block(du, bid, out_st),
        equals=lambda a, b: a == b,
    )

    by_id = program.block_by_id()
    live_before_cmd: dict[ProgramPoint, tuple[str, ...]] = {}
    live_after_cmd: dict[ProgramPoint, tuple[str, ...]] = {}

    for bid, block in by_id.items():
        defs_by_idx: dict[int, list[str]] = defaultdict(list)
        uses_by_idx: dict[int, list[str]] = defaultdict(list)
        for ds in du.by_block[bid].definition_sites:
            defs_by_idx[ds.cmd_index].append(ds.symbol)
        for us in du.by_block[bid].use_sites:
            uses_by_idx[us.cmd_index].append(us.symbol)

        live = set(block_out.get(bid, frozenset()))
        for idx in range(len(block.commands) - 1, -1, -1):
            pt = ProgramPoint(bid, idx)
            live_after_cmd[pt] = tuple(sorted(live))
            for sym in defs_by_idx.get(idx, []):
                live.discard(sym)
            for sym in uses_by_idx.get(idx, []):
                live.add(sym)
            live_before_cmd[pt] = tuple(sorted(live))

    return LivenessResult(
        live_in_by_block={bid: tuple(sorted(v)) for bid, v in block_in.items()},
        live_out_by_block={bid: tuple(sorted(v)) for bid, v in block_out.items()},
        live_before_command=live_before_cmd,
        live_after_command=live_after_cmd,
    )


def eliminate_dead_assignments(
    program: TacProgram,
    *,
    strip_var_suffixes: bool = True,
    liveness: LivenessResult | None = None,
) -> DceResult:
    lv = liveness if liveness is not None else analyze_liveness(program, strip_var_suffixes=strip_var_suffixes)
    removed: list[DeadAssignment] = []
    new_blocks: list[TacBlock] = []

    for block in program.blocks:
        kept_cmds = []
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, (AssignExpCmd, AssignHavocCmd)):
                sym = canonical_symbol(cmd.lhs, strip_var_suffixes=strip_var_suffixes)
                live_after = set(lv.live_after_command.get(ProgramPoint(block.id, idx), tuple()))
                if sym not in live_after:
                    removed.append(
                        DeadAssignment(
                            symbol=sym,
                            block_id=block.id,
                            cmd_index=idx,
                            cmd_kind=type(cmd).__name__,
                            raw=cmd.raw,
                        )
                    )
                    continue
            kept_cmds.append(cmd)
        new_blocks.append(replace(block, commands=kept_cmds))

    return DceResult(removed=tuple(removed), program=TacProgram(blocks=new_blocks))


def analyze_dsa(
    program: TacProgram,
    *,
    strip_var_suffixes: bool = True,
    def_use: DefUseResult | None = None,
    reaching_defs: ReachingDefinitionsResult | None = None,
) -> DsaResult:
    du = def_use if def_use is not None else extract_def_use(program, strip_var_suffixes=strip_var_suffixes)
    by_id = program.block_by_id()
    succs: dict[str, tuple[str, ...]] = {
        b.id: tuple(s for s in b.successors if s in by_id) for b in program.blocks
    }

    def _is_dynamic_symbol(defs: tuple[DefinitionSite, ...]) -> bool:
        # Dynamic definition conditions:
        # (a) symbol has multiple definitions
        # (b) all definitions are in different blocks
        # (c) all those blocks have the same unique successor
        if len(defs) <= 1:
            return False
        def_blocks = [d.block_id for d in defs]
        uniq_blocks = set(def_blocks)
        if len(uniq_blocks) != len(def_blocks):
            return False
        uniq_succs: set[str] = set()
        for bid in uniq_blocks:
            out = succs.get(bid, tuple())
            if len(out) != 1:
                return False
            uniq_succs.add(out[0])
        return len(uniq_succs) == 1

    issues: list[DsaIssue] = []
    dynamic_assignments: list[DsaDynamicAssignment] = []
    dynamic_symbols = {
        sym for sym, defs in du.definitions_by_symbol.items() if _is_dynamic_symbol(defs)
    }

    # Dynamic assignment: every assignment to a symbol that satisfies the
    # DSA "dynamic definition" conditions.
    defs_by_symbol = du.definitions_by_symbol
    for sym in sorted(dynamic_symbols):
        defs = defs_by_symbol[sym]
        for ds in defs:
            sib = tuple(
                sorted(
                    f"{d.block_id}:{d.cmd_index}"
                    for d in defs
                    if d.block_id != ds.block_id or d.cmd_index != ds.cmd_index
                )
            )
            dynamic_assignments.append(
                DsaDynamicAssignment(
                    symbol=sym,
                    block_id=ds.block_id,
                    cmd_index=ds.cmd_index,
                    cmd_kind=ds.cmd_kind,
                    raw=ds.raw,
                    sibling_defs=sib,
                )
            )

    # Block shape check with dynamic classification from DSA conditions:
    # (static)*(dynamic)*terminator
    for block in program.blocks:
        defs_by_idx: dict[int, list[DefinitionSite]] = defaultdict(list)
        for ds in du.by_block[block.id].definition_sites:
            defs_by_idx[ds.cmd_index].append(ds)

        seen_dynamic = False
        seen_terminator = False
        for idx, cmd in enumerate(block.commands):
            cmd_kind = type(cmd).__name__
            is_term = cmd_kind in {"JumpCmd", "JumpiCmd"}
            defs_here = defs_by_idx.get(idx, [])
            if defs_here:
                if seen_terminator:
                    issues.append(
                        DsaIssue(
                            kind="shape",
                            symbol=None,
                            block_id=block.id,
                            cmd_index=idx,
                            detail="assignment appears after terminator",
                        )
                    )
                dyn_here = any(ds.symbol in dynamic_symbols for ds in defs_here)
                stat_here = any(ds.symbol not in dynamic_symbols for ds in defs_here)
                if stat_here and seen_dynamic:
                    issues.append(
                        DsaIssue(
                            kind="shape",
                            symbol=None,
                            block_id=block.id,
                            cmd_index=idx,
                            detail="static assignment appears after dynamic assignment",
                        )
                    )
                if dyn_here:
                    seen_dynamic = True
            else:
                if seen_terminator and not is_term:
                    issues.append(
                        DsaIssue(
                            kind="shape",
                            symbol=None,
                            block_id=block.id,
                            cmd_index=idx,
                            detail=f"non-terminator command {cmd_kind} appears after terminator",
                        )
                    )
            if is_term:
                seen_terminator = True

    if reaching_defs is not None:
        rd = reaching_defs
        for block in program.blocks:
            bdu = du.by_block[block.id]
            uses_by_idx: dict[int, list] = defaultdict(list)
            for us in bdu.use_sites:
                uses_by_idx[us.cmd_index].append(us)
            for idx, _cmd in enumerate(block.commands):
                pt = ProgramPoint(block.id, idx)
                reaching_here = rd.in_by_command.get(pt, {})
                for us in uses_by_idx.get(idx, []):
                    defs = reaching_here.get(us.symbol, tuple())
                    if len(defs) <= 1:
                        continue
                    if us.symbol not in dynamic_symbols:
                        issues.append(
                            DsaIssue(
                                kind="ambiguous-use",
                                symbol=us.symbol,
                                block_id=us.block_id,
                                cmd_index=us.cmd_index,
                                detail="multiple reaching defs for non-dynamic symbol",
                            )
                        )
        uniq_issues = tuple(dict.fromkeys(issues))
        return DsaResult(issues=uniq_issues, dynamic_assignments=tuple(dynamic_assignments))

    block_in_fast, _ = _compute_reaching_block_states(program, du=du)
    for block in program.blocks:
        bdu = du.by_block[block.id]
        state: RDStateFast = dict(block_in_fast.get(block.id, {}))
        uses_by_idx: dict[int, list] = defaultdict(list)
        defs_by_idx: dict[int, list[DefinitionSite]] = defaultdict(list)
        for ds in bdu.definition_sites:
            defs_by_idx[ds.cmd_index].append(ds)
        for us in bdu.use_sites:
            uses_by_idx[us.cmd_index].append(us)
        for idx, _cmd in enumerate(block.commands):
            for us in uses_by_idx.get(idx, []):
                mask = state.get(us.symbol_id, 0)
                if mask.bit_count() <= 1:
                    continue
                if us.symbol not in dynamic_symbols:
                    issues.append(
                        DsaIssue(
                            kind="ambiguous-use",
                            symbol=us.symbol,
                            block_id=us.block_id,
                            cmd_index=us.cmd_index,
                            detail="multiple reaching defs for non-dynamic symbol",
                        )
                    )
            for ds in defs_by_idx.get(idx, []):
                state[ds.symbol_id] = 1 << ds.def_id
    uniq_issues = tuple(dict.fromkeys(issues))
    return DsaResult(issues=uniq_issues, dynamic_assignments=tuple(dynamic_assignments))


def analyze_control_dependence(program: TacProgram) -> ControlDependenceResult:
    blocks = [b.id for b in program.blocks]
    by_id = program.block_by_id()
    succ = {bid: [s for s in by_id[bid].successors if s in by_id] for bid in by_id}
    exits = [bid for bid, out in succ.items() if not out]

    all_nodes = set(blocks)
    postdom: dict[str, set[str]] = {}
    for b in blocks:
        if b in exits:
            postdom[b] = {b}
        else:
            postdom[b] = set(all_nodes)

    changed = True
    while changed:
        changed = False
        for b in blocks:
            if b in exits:
                continue
            succs = succ.get(b, [])
            if not succs:
                new_set = {b}
            else:
                inter = set(postdom[succs[0]])
                for s in succs[1:]:
                    inter &= postdom[s]
                new_set = {b} | inter
            if new_set != postdom[b]:
                postdom[b] = new_set
                changed = True

    edges: set[tuple[str, str]] = set()
    for b in blocks:
        succs = succ.get(b, [])
        if len(succs) < 2:
            continue
        for s in succs:
            for y in postdom[s]:
                if y not in postdom[b]:
                    edges.add((b, y))

    return ControlDependenceResult(
        edges=tuple(sorted(edges)),
        postdominators={bid: tuple(sorted(nodes)) for bid, nodes in postdom.items()},
    )
