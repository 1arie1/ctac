from __future__ import annotations

from dataclasses import dataclass

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import JumpiCmd
from ctac.ir.models import TacBlock, TacProgram


def sanitize_ident(raw: str) -> str:
    out = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in raw)
    if not out:
        return "_"
    if out[0].isdigit():
        return "_" + out
    return out


def blk_var_name(block_id: str) -> str:
    return f"BLK_{sanitize_ident(block_id)}"


def block_guard(block_id: str, *, entry_block_id: str) -> str:
    return "true" if block_id == entry_block_id else blk_var_name(block_id)


# Production pipeline's reachability-bool naming convention. The TAC
# ships ``ReachabilityCertora<block-id>`` as a free havoc'd Bool that
# the encoder aliases to the matching ``BLK_<id>``. ``ctac pin`` uses
# the same convention to fold RC vars to false when their block is
# dropped.
_RC_PREFIX = "ReachabilityCertora"


def reachability_var_name(block_id: str) -> str:
    """Return the reachability-bool variable name for ``block_id``."""
    return f"{_RC_PREFIX}{block_id}"


def is_reachability_var(name: str) -> bool:
    """True if ``name`` matches the reachability-bool naming convention."""
    return name.startswith(_RC_PREFIX) and len(name) > len(_RC_PREFIX)


def block_id_for_reachability_var(name: str) -> str | None:
    """Inverse of :func:`reachability_var_name`. Returns ``None`` if
    ``name`` is not a reachability-bool name."""
    if not is_reachability_var(name):
        return None
    return name[len(_RC_PREFIX):]


@dataclass(frozen=True)
class PredEdge:
    pred_block_id: str
    succ_block_id: str
    branch_cond: str


def predecessor_edges(program: TacProgram, *, symbol_term_by_name: dict[str, str]) -> dict[str, list[PredEdge]]:
    by_id = program.block_by_id()
    out: dict[str, list[PredEdge]] = {b.id: [] for b in program.blocks}
    for pred in program.blocks:
        if pred.commands and isinstance(pred.commands[-1], JumpiCmd):
            j = pred.commands[-1]
            cond_sym = canonical_symbol(j.condition, strip_var_suffixes=True)
            cond = symbol_term_by_name.get(cond_sym, sanitize_ident(cond_sym))
            for succ in pred.successors:
                if succ not in by_id:
                    continue
                if succ == j.then_target:
                    branch = cond
                elif succ == j.else_target:
                    branch = f"(not {cond})"
                else:
                    branch = "false"
                out[succ].append(PredEdge(pred_block_id=pred.id, succ_block_id=succ, branch_cond=branch))
            continue
        for succ in pred.successors:
            if succ not in by_id:
                continue
            out[succ].append(PredEdge(pred_block_id=pred.id, succ_block_id=succ, branch_cond="true"))
    return out


@dataclass(frozen=True)
class BranchCondition:
    block_id: str
    cond: str  # encoded SMT term for the JumpiCmd condition symbol
    then_target: str
    else_target: str


def branch_conditions(
    program: TacProgram, *, symbol_term_by_name: dict[str, str]
) -> dict[str, BranchCondition]:
    """Per controlling block, its branch condition and the two targets.

    The controller-keyed complement to :func:`predecessor_edges` (which
    is successor-keyed). ``cond`` is lowered identically to
    ``predecessor_edges`` so a gamma gate built from it references the
    *same* symbol the CFG-constraint layer uses — wiring the branch
    condition once into both planes. Only blocks whose terminator is a
    ``JumpiCmd`` appear; unconditional edges carry no gate.
    """
    out: dict[str, BranchCondition] = {}
    for blk in program.blocks:
        if not blk.commands or not isinstance(blk.commands[-1], JumpiCmd):
            continue
        j = blk.commands[-1]
        cond_sym = canonical_symbol(j.condition, strip_var_suffixes=True)
        cond = symbol_term_by_name.get(cond_sym, sanitize_ident(cond_sym))
        out[blk.id] = BranchCondition(
            block_id=blk.id,
            cond=cond,
            then_target=j.then_target,
            else_target=j.else_target,
        )
    return out


def block_by_id(program: TacProgram, block_id: str) -> TacBlock:
    by_id = program.block_by_id()
    if block_id not in by_id:
        raise ValueError(f"unknown block id: {block_id}")
    return by_id[block_id]
