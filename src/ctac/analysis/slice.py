"""Backward static slicing over TAC programs.

The slicer follows data dependences (via reaching definitions) and
control dependences (via post-dominance) backwards from a set of seed
``ProgramPoint``s, producing a ``frozenset[ProgramPoint]`` that names
every command "in" the slice. The result is a pure display filter:
slices are not required to be encodable. The CLI walks blocks itself
and asks each ``ProgramPoint`` whether it is selected.

Criterion forms (resolved by callers; the library itself takes
``SliceCriterion`` objects):

- ``symbol``: every def of the canonical symbol. In DSA this is
  almost always a single program point; for dynamic registers it is
  the predecessor sibling defs that all flow into the same successor.
- ``symbol_in_block``: the def(s) of the canonical symbol within one
  specific block. Used to disambiguate dynamic registers.
- ``last_assert_in_block``: the last ``AssertCmd`` in a block (in
  source order). Most blocks have at most one assert; this resolves
  cleanly when the block has exactly one or several.
- ``whole_block``: every command in a block as a seed.
- ``point``: an explicit ``ProgramPoint``. The CLI does not expose
  this form (cmd indices are unstable for users because annotations
  occupy slots), but the library accepts it for callers that already
  hold ``ProgramPoint`` coordinates from another analysis.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Sequence
from dataclasses import dataclass, field

from ctac.analysis.defuse import extract_def_use
from ctac.analysis.expr_walk import command_uses, command_weak_uses
from ctac.analysis.model import (
    ControlDependenceResult,
    DefUseResult,
    ProgramPoint,
    ReachingDefinitionsResult,
)
from ctac.analysis.passes import (
    analyze_control_dependence,
    analyze_reaching_definitions,
)
from ctac.ast.nodes import AssertCmd
from ctac.ir.models import TacProgram


@dataclass(frozen=True)
class SliceCriterion:
    """One seed for the slicer. Exactly one field should be set."""

    symbol: str | None = None
    symbol_in_block: tuple[str, str] | None = None  # (symbol, block_id)
    last_assert_in_block: str | None = None
    whole_block: str | None = None
    point: ProgramPoint | None = None


@dataclass(frozen=True)
class SliceConfig:
    follow_data: bool = True
    follow_control: bool = True
    include_weak_uses: bool = False
    max_depth: int | None = None
    strip_var_suffixes: bool = True


@dataclass(frozen=True)
class SliceResult:
    selected: frozenset[ProgramPoint]
    seeds: tuple[ProgramPoint, ...]
    rounds: int
    warnings: tuple[str, ...] = field(default_factory=tuple)


class SliceCriterionError(ValueError):
    """Raised when a criterion cannot be resolved against the program."""


def _resolve_criterion(
    crit: SliceCriterion,
    *,
    program: TacProgram,
    du: DefUseResult,
) -> tuple[list[ProgramPoint], list[str]]:
    by_id = program.block_by_id()
    warnings: list[str] = []
    points: list[ProgramPoint] = []

    if crit.point is not None:
        if crit.point.block_id not in by_id:
            raise SliceCriterionError(f"unknown block: {crit.point.block_id!r}")
        block = by_id[crit.point.block_id]
        if not (0 <= crit.point.cmd_index < len(block.commands)):
            raise SliceCriterionError(
                f"cmd index {crit.point.cmd_index} out of range "
                f"for block {crit.point.block_id} ({len(block.commands)} cmds)"
            )
        points.append(crit.point)

    if crit.whole_block is not None:
        if crit.whole_block not in by_id:
            raise SliceCriterionError(f"unknown block: {crit.whole_block!r}")
        block = by_id[crit.whole_block]
        for idx, _cmd in enumerate(block.commands):
            points.append(ProgramPoint(block.id, idx))

    if crit.last_assert_in_block is not None:
        if crit.last_assert_in_block not in by_id:
            raise SliceCriterionError(
                f"unknown block: {crit.last_assert_in_block!r}"
            )
        block = by_id[crit.last_assert_in_block]
        last_assert_idx: int | None = None
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, AssertCmd):
                last_assert_idx = idx
        if last_assert_idx is None:
            raise SliceCriterionError(
                f"block {crit.last_assert_in_block!r} has no AssertCmd"
            )
        points.append(ProgramPoint(block.id, last_assert_idx))

    if crit.symbol is not None:
        sites = du.definitions_by_symbol.get(crit.symbol, ())
        if not sites:
            warnings.append(f"symbol has no definitions: {crit.symbol!r}")
        for ds in sites:
            points.append(ProgramPoint(ds.block_id, ds.cmd_index))

    if crit.symbol_in_block is not None:
        sym, bid = crit.symbol_in_block
        if bid not in by_id:
            raise SliceCriterionError(f"unknown block: {bid!r}")
        sites = [
            ds
            for ds in du.definitions_by_symbol.get(sym, ())
            if ds.block_id == bid
        ]
        if not sites:
            warnings.append(
                f"symbol {sym!r} has no definitions in block {bid!r}"
            )
        for ds in sites:
            points.append(ProgramPoint(ds.block_id, ds.cmd_index))

    return points, warnings


def _block_index_of_terminator(program: TacProgram) -> dict[str, int]:
    """Map block_id -> index of the last command in the block.

    Used to identify the controlling command (the JumpiCmd) of any
    block named as a controller in the control-dependence graph.
    """
    out: dict[str, int] = {}
    for b in program.blocks:
        if b.commands:
            out[b.id] = len(b.commands) - 1
    return out


def _controllers_of(cd: ControlDependenceResult) -> dict[str, list[str]]:
    """Build dependent_block_id -> [controller_block_id, ...]."""
    out: dict[str, list[str]] = {}
    for ctrl, dep in cd.edges:
        out.setdefault(dep, []).append(ctrl)
    return out


def compute_slice(
    program: TacProgram,
    criteria: Sequence[SliceCriterion],
    config: SliceConfig = SliceConfig(),
    *,
    def_use: DefUseResult | None = None,
    reaching_defs: ReachingDefinitionsResult | None = None,
    control_dep: ControlDependenceResult | None = None,
) -> SliceResult:
    """Backward static slice over ``program`` from ``criteria``.

    The fixpoint adds a command ``c`` to the slice when some sliced
    command uses a symbol whose reaching def is ``c`` (data) or when
    some sliced command's block is control-dependent on ``c``'s block
    and ``c`` is that block's terminator (control).

    Bytemap chains fall out for free: ``Select(M, k)`` uses ``M`` and
    ``k``, so the reaching def of ``M`` (a prior ``Store``) joins the
    slice on the next round, which then pulls its key/value subtree.
    """
    du = (
        def_use
        if def_use is not None
        else extract_def_use(program, strip_var_suffixes=config.strip_var_suffixes)
    )

    seeds: list[ProgramPoint] = []
    warnings: list[str] = []
    for crit in criteria:
        pts, ws = _resolve_criterion(crit, program=program, du=du)
        seeds.extend(pts)
        warnings.extend(ws)

    if not seeds:
        return SliceResult(
            selected=frozenset(),
            seeds=(),
            rounds=0,
            warnings=tuple(warnings),
        )

    rd: ReachingDefinitionsResult | None = None
    if config.follow_data:
        rd = (
            reaching_defs
            if reaching_defs is not None
            else analyze_reaching_definitions(program, def_use=du)
        )

    cd: ControlDependenceResult | None = None
    controllers: dict[str, list[str]] = {}
    term_idx: dict[str, int] = {}
    if config.follow_control:
        cd = (
            control_dep
            if control_dep is not None
            else analyze_control_dependence(program)
        )
        controllers = _controllers_of(cd)
        term_idx = _block_index_of_terminator(program)

    by_id = program.block_by_id()
    selected: set[ProgramPoint] = set(seeds)
    work: deque[ProgramPoint] = deque(dict.fromkeys(seeds))
    rounds = 0
    cap = config.max_depth if config.max_depth is not None else -1

    while work:
        if cap >= 0 and rounds >= cap:
            break
        rounds += 1
        next_work: deque[ProgramPoint] = deque()

        while work:
            pt = work.popleft()
            block = by_id.get(pt.block_id)
            if block is None or not (0 <= pt.cmd_index < len(block.commands)):
                continue
            cmd = block.commands[pt.cmd_index]

            if config.follow_data and rd is not None:
                uses = command_uses(
                    cmd, strip_var_suffixes=config.strip_var_suffixes
                )
                weak = (
                    command_weak_uses(
                        cmd, strip_var_suffixes=config.strip_var_suffixes
                    )
                    if config.include_weak_uses
                    else ()
                )
                in_here = rd.in_by_command.get(pt, {})
                for sym in (*uses, *weak):
                    for ds in in_here.get(sym, ()):
                        cand = ProgramPoint(ds.block_id, ds.cmd_index)
                        if cand not in selected:
                            selected.add(cand)
                            next_work.append(cand)

            if config.follow_control:
                for ctrl_bid in controllers.get(pt.block_id, ()):
                    last = term_idx.get(ctrl_bid)
                    if last is None:
                        continue
                    cand = ProgramPoint(ctrl_bid, last)
                    if cand not in selected:
                        selected.add(cand)
                        next_work.append(cand)

        work = next_work

    return SliceResult(
        selected=frozenset(selected),
        seeds=tuple(dict.fromkeys(seeds)),
        rounds=rounds,
        warnings=tuple(warnings),
    )
