"""DSA/SSA well-formedness checker for Tiny TAC.

Establishes that every variable is *determined by its definition*. A
variable is one of:

- **static** - a single definition;
- **phi** - defined by exactly one ``phi`` command;
- **dynamic** - several non-phi definitions in distinct sibling
  predecessor blocks that share one common successor.

A program may mix phi nodes and dynamic assignments across different
variables; that is well-formed (DSA is a superset of SSA). The checker
validates each variable against the discipline its definitions imply,
plus the per-block shape rules (phi prefix, dynamic suffix) and an
ambiguous-use check driven by reaching definitions.

Mirrors ``ctac.analysis.passes.analyze_dsa``; reaching definitions reuse
networkx for predecessors and topological order.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass

from ctac.ttac import ast

from . import cfg
from .defuse import DefSite, DefUse, cmd_defs, extract_def_use


@dataclass(frozen=True)
class DsaIssue:
    kind: str  # "shape" | "phi" | "over-definition" | "ambiguous-use"
    detail: str
    block: str
    cmd_index: int
    symbol: str | None = None


@dataclass(frozen=True)
class DsaDynamicAssignment:
    symbol: str
    block: str
    cmd_index: int
    sibling_defs: tuple[str, ...]


@dataclass(frozen=True)
class DsaResult:
    issues: tuple[DsaIssue, ...]
    dynamic_assignments: tuple[DsaDynamicAssignment, ...]
    static: frozenset[str]
    phi: frozenset[str]
    dynamic: frozenset[str]

    @property
    def is_valid(self) -> bool:
        return not self.issues


def _succ_map(program: ast.Program) -> dict[str, tuple[str, ...]]:
    labels = {b.label for b in program.blocks}
    return {
        b.label: tuple(s for s in cfg.successors(b) if s in labels)
        for b in program.blocks
    }


def _is_dynamic(defs: tuple[DefSite, ...], succ: dict[str, tuple[str, ...]]) -> bool:
    # multiple defs, all in distinct blocks, each block with a single
    # successor, all sharing the same one (the merge point).
    if len(defs) <= 1:
        return False
    def_blocks = [d.block for d in defs]
    uniq = set(def_blocks)
    if len(uniq) != len(def_blocks):
        return False
    merge: set[str] = set()
    for bid in uniq:
        out = succ.get(bid, ())
        if len(out) != 1:
            return False
        merge.add(out[0])
    return len(merge) == 1


def _reaching_block_in(program: ast.Program, du: DefUse) -> dict[str, dict[int, int]]:
    preds = cfg.predecessors(program)
    order = cfg.topo_order(program)

    def transfer(label: str, in_state: dict[int, int]) -> dict[int, int]:
        cur = dict(in_state)
        for ds in du.by_block[label].def_sites:
            cur[ds.symbol_id] = 1 << ds.def_id
        return cur

    block_in: dict[str, dict[int, int]] = {b.label: {} for b in program.blocks}
    block_out: dict[str, dict[int, int]] = {
        label: transfer(label, {}) for label in block_in
    }

    changed = True
    while changed:
        changed = False
        for label in order:
            merged: dict[int, int] = {}
            for p in preds[label]:
                for sid, mask in block_out[p].items():
                    merged[sid] = merged.get(sid, 0) | mask
            if merged != block_in[label]:
                block_in[label] = merged
                changed = True
            new_out = transfer(label, merged)
            if new_out != block_out[label]:
                block_out[label] = new_out
                changed = True
    return block_in


def check_dsa(program: ast.Program, *, def_use: DefUse | None = None) -> DsaResult:
    du = def_use if def_use is not None else extract_def_use(program)
    succ = _succ_map(program)
    preds = cfg.predecessors(program)

    issues: list[DsaIssue] = []
    static: set[str] = set()
    phi: set[str] = set()
    dynamic: set[str] = set()

    # --- per-variable classification ---
    for sym, defs in du.defs_by_symbol.items():
        phi_defs = [d for d in defs if d.kind == "Phi"]
        if phi_defs:
            if len(defs) == 1:
                phi.add(sym)
            else:
                d0 = defs[0]
                issues.append(DsaIssue(
                    kind="over-definition", symbol=sym, block=d0.block,
                    cmd_index=d0.cmd_index,
                    detail="phi definition mixed with other definitions",
                ))
        elif len(defs) == 1:
            static.add(sym)
        elif _is_dynamic(defs, succ):
            dynamic.add(sym)
        else:
            d0 = defs[0]
            issues.append(DsaIssue(
                kind="over-definition", symbol=sym, block=d0.block,
                cmd_index=d0.cmd_index,
                detail="multiple definitions that are neither phi nor a valid dynamic merge",
            ))

    dynamic_assignments: list[DsaDynamicAssignment] = []
    for sym in sorted(dynamic):
        defs = du.defs_by_symbol[sym]
        for d in defs:
            sib = tuple(sorted(
                f"{o.block}:{o.cmd_index}" for o in defs
                if (o.block, o.cmd_index) != (d.block, d.cmd_index)
            ))
            dynamic_assignments.append(DsaDynamicAssignment(
                symbol=sym, block=d.block, cmd_index=d.cmd_index, sibling_defs=sib,
            ))

    # --- per-block shape: phi prefix, dynamic suffix ---
    for block in program.blocks:
        seen_nonphi = False
        seen_dynamic = False
        for idx, cmd in enumerate(block.commands):
            is_phi = isinstance(cmd, ast.Phi)
            if is_phi and seen_nonphi:
                issues.append(DsaIssue(
                    kind="shape", block=block.label, cmd_index=idx,
                    detail="phi command must be in the block's prefix",
                ))
            if not is_phi:
                seen_nonphi = True

            targets = cmd_defs(cmd)
            dyn_here = any(t.name in dynamic for t in targets)
            if seen_dynamic and not dyn_here:
                issues.append(DsaIssue(
                    kind="shape", block=block.label, cmd_index=idx,
                    detail="dynamic assignments must form a contiguous suffix "
                           "before the terminator",
                ))
            if dyn_here:
                seen_dynamic = True

    # --- phi arity: one arm per predecessor, labels match ---
    for block in program.blocks:
        pred_set = set(preds[block.label])
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, ast.Phi):
                continue
            arm_labels = [a.label for a in cmd.arms]
            if set(arm_labels) != pred_set or len(arm_labels) != len(pred_set):
                issues.append(DsaIssue(
                    kind="phi", symbol=cmd.target.name, block=block.label,
                    cmd_index=idx,
                    detail=f"phi arms {sorted(set(arm_labels))} do not match "
                           f"predecessors {sorted(pred_set)}",
                ))

    # --- ambiguous use: a non-dynamic symbol reached by >1 definition ---
    block_in = _reaching_block_in(program, du)
    for block in program.blocks:
        bdu = du.by_block[block.label]
        defs_by_idx: dict[int, list[DefSite]] = defaultdict(list)
        for ds in bdu.def_sites:
            defs_by_idx[ds.cmd_index].append(ds)
        uses_by_idx: dict[int, list] = defaultdict(list)
        for us in bdu.use_sites:
            uses_by_idx[us.cmd_index].append(us)

        state = dict(block_in[block.label])
        n = len(block.commands)
        for idx in range(n + 1):  # +1 covers terminator uses
            for us in uses_by_idx.get(idx, []):
                mask = state.get(du.symbol_to_id.get(us.symbol, -1), 0)
                if mask.bit_count() > 1 and us.symbol not in dynamic:
                    issues.append(DsaIssue(
                        kind="ambiguous-use", symbol=us.symbol,
                        block=us.block, cmd_index=us.cmd_index,
                        detail="multiple reaching definitions for a non-dynamic symbol",
                    ))
            for ds in defs_by_idx.get(idx, []):
                state[ds.symbol_id] = 1 << ds.def_id

    uniq = tuple(dict.fromkeys(issues))
    return DsaResult(
        issues=uniq,
        dynamic_assignments=tuple(dynamic_assignments),
        static=frozenset(static),
        phi=frozenset(phi),
        dynamic=frozenset(dynamic),
    )
