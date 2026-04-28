"""Per-variable diagnostic for the interval domain.

``explain_var(program, var, *, symbol_sorts)`` returns a structured
``VarExplanation`` answering "where does this value come from?"
questions: classification (DSA-static vs dynamic), sort, def sites,
the assume commands that refine the var, and the per-block view.
The CLI surfaces it via ``ctac absint --explain VAR``.

Why this shape: the headline "tightest static intervals" table is a
*meet across views*, which is the strongest fact known at *some*
program point — it is NOT a universal value. When a real-target
report shows a var pinned to an unexpectedly tight value (e.g.
``[0, 0]`` for a register that obviously isn't always zero), the
explanation is almost always "one block's local refines it that
tight; other blocks see a wider value". This module makes the
distinction visible.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from ctac.analysis.abs_int.domains.interval import (
    IntervalResult,
    analyze_intervals,
)
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.analysis.abs_int.interval_ops import meet as iv_meet
from ctac.analysis.defuse import extract_def_use
from ctac.analysis.passes import analyze_dsa
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    SymbolRef,
    TacExpr,
)
from ctac.ir.models import NBId, TacProgram


@dataclass(frozen=True)
class DefSite:
    block_id: str
    cmd_index: int
    cmd_kind: str
    rhs_text: str  # raw rhs (or "" for havoc)


@dataclass(frozen=True)
class RefinementSite:
    block_id: str
    cmd_index: int
    cond_text: str
    local_value: Interval  # value of var in local[block_id] at analysis end


@dataclass(frozen=True)
class VarExplanation:
    var: str
    sort: str | None
    is_dsa_dynamic: bool
    static: Interval | None  # None when the var has no static entry
    defs: tuple[DefSite, ...]
    refinements: tuple[RefinementSite, ...]
    per_block_view: tuple[tuple[NBId, Interval], ...]
    tightest: Interval
    sort_default: Interval


def explain_var(
    program: TacProgram,
    var: str,
    *,
    result: IntervalResult | None = None,
    symbol_sorts: Mapping[str, str] | None = None,
) -> VarExplanation:
    """Build a `VarExplanation` for `var`. Re-runs the analysis if no
    `result` is passed."""
    sorts = dict(symbol_sorts or {})
    if result is None:
        result = analyze_intervals(program, symbol_sorts=sorts)

    sort = sorts.get(var)
    sort_default = _sort_default(sort)

    dsa = analyze_dsa(program)
    dynamic_set = {a.symbol for a in dsa.dynamic_assignments}
    is_dynamic = var in dynamic_set

    du = extract_def_use(program)
    defs = []
    for ds in du.definitions_by_symbol.get(var, ()):
        cmd = _cmd_at(program, ds.block_id, ds.cmd_index)
        rhs_text = ""
        if isinstance(cmd, AssignExpCmd):
            rhs_text = _render(cmd.rhs)
        defs.append(
            DefSite(
                block_id=ds.block_id,
                cmd_index=ds.cmd_index,
                cmd_kind=ds.cmd_kind,
                rhs_text=rhs_text,
            )
        )

    refinements: list[RefinementSite] = []
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, AssumeExpCmd):
                continue
            if not _refers_to(cmd.condition, var):
                continue
            local_iv = result.per_block_local.get(block.id, {}).get(var)
            if local_iv is None:
                # The assume mentions the var but didn't end up storing
                # to local — typically because the refinement was
                # promoted into static (entry block, DSA-static).
                local_iv = result.static.get(var, Interval(None, None))
            refinements.append(
                RefinementSite(
                    block_id=block.id,
                    cmd_index=idx,
                    cond_text=_render(cmd.condition),
                    local_value=local_iv,
                )
            )

    per_block_view: list[tuple[NBId, Interval]] = []
    for block_id in sorted(result.per_block_local):
        iv = result.per_block_local[block_id].get(var)
        if iv is None:
            continue
        per_block_view.append((block_id, iv))

    # Tightest: meet across static + every per-block local. Same
    # formula the CLI's "tightest static intervals" table uses.
    tightest = result.static.get(var, Interval(None, None))
    for _, iv in per_block_view:
        tightest = iv_meet(tightest, iv)

    return VarExplanation(
        var=var,
        sort=sort,
        is_dsa_dynamic=is_dynamic,
        static=result.static.get(var),
        defs=tuple(defs),
        refinements=tuple(refinements),
        per_block_view=tuple(per_block_view),
        tightest=tightest,
        sort_default=sort_default,
    )


def format_var_explanation(exp: VarExplanation) -> list[str]:
    """Plain-text rendering for `--plain` mode."""
    lines: list[str] = []
    lines.append(f"explain {exp.var}:")
    lines.append(f"  sort: {exp.sort or '(unknown)'}")
    klass = "DSA-dynamic (multiple defs)" if exp.is_dsa_dynamic else "DSA-static (single def or none)"
    lines.append(f"  classification: {klass}")
    lines.append(f"  sort_default: {_fmt(exp.sort_default)}")
    lines.append(
        f"  static: {_fmt(exp.static) if exp.static is not None else '(no entry)'}"
    )
    if exp.defs:
        lines.append(f"  defs ({len(exp.defs)}):")
        for d in exp.defs:
            tail = f"  rhs: {d.rhs_text}" if d.rhs_text else ""
            lines.append(
                f"    {d.block_id}:{d.cmd_index}  {d.cmd_kind}{tail}"
            )
    else:
        lines.append("  defs: (none — symbol used without a def in this program)")
    if exp.refinements:
        lines.append(f"  refining assumes ({len(exp.refinements)}):")
        for r in exp.refinements:
            lines.append(
                f"    {r.block_id}:{r.cmd_index}  {r.cond_text}"
                f"  -> {_fmt(r.local_value)}"
            )
    else:
        lines.append("  refining assumes: (none)")
    if exp.per_block_view:
        # Show distinct values across blocks; collapse runs with the
        # same interval.
        lines.append("  per-block view (where var has a local entry):")
        # Group consecutive blocks with the same interval.
        groups: list[tuple[Interval, list[str]]] = []
        for bid, iv in exp.per_block_view:
            if groups and groups[-1][0] == iv:
                groups[-1][1].append(bid)
            else:
                groups.append((iv, [bid]))
        for iv, bids in groups:
            if len(bids) == 1:
                lines.append(f"    {bids[0]}: {_fmt(iv)}")
            else:
                lines.append(
                    f"    {len(bids)} blocks at {_fmt(iv)}: "
                    f"{bids[0]} ... {bids[-1]}"
                )
    else:
        lines.append("  per-block view: (no local entries)")
    lines.append(f"  tightest (meet across views): {_fmt(exp.tightest)}")
    distinct_views = {iv for _, iv in exp.per_block_view}
    distinct_views.discard(exp.tightest)
    static_diverges = exp.static is not None and exp.static != exp.tightest
    if distinct_views or static_diverges:
        # The tightest is sharper than what at least one block (or the
        # universal `static`) would give on its own. Make the meet
        # nature explicit so the headline tightest-table isn't misread
        # as a universal value.
        tight_blocks = [
            bid for bid, iv in exp.per_block_view if iv == exp.tightest
        ]
        lines.append(
            "  note: tightest is the meet across views, NOT a universal "
            "value."
        )
        if exp.per_block_view:
            lines.append(
                f"        var takes this tight value at "
                f"{len(tight_blocks)}/{len(exp.per_block_view)} block(s) "
                f"with local entries; blocks without a local entry see "
                f"the static / sort-default value."
            )
        else:
            lines.append(
                "        no per-block local entries; the tightest comes "
                "from static alone."
            )
    return lines


# --------------------------------------------------------------------
# Helpers


def _sort_default(sort: str | None) -> Interval:
    if sort == "bool":
        return Interval(0, 1)
    if sort and sort.startswith("bv"):
        rest = sort[2:]
        if rest.isdigit():
            w = int(rest)
            return Interval(0, (1 << w) - 1)
    return Interval(None, None)


def _cmd_at(program: TacProgram, block_id: str, cmd_index: int):
    by_id = program.block_by_id()
    block = by_id.get(block_id)
    if block is None or cmd_index >= len(block.commands):
        return None
    return block.commands[cmd_index]


def _refers_to(expr: TacExpr, var: str) -> bool:
    if isinstance(expr, SymbolRef):
        return expr.name == var
    if isinstance(expr, ApplyExpr):
        return any(_refers_to(a, var) for a in expr.args)
    return False


def _render(expr: TacExpr) -> str:
    """Compact stringifier for AST → diagnostic display."""
    if isinstance(expr, SymbolRef):
        return expr.name
    if isinstance(expr, ApplyExpr):
        return f"{expr.op}({' '.join(_render(a) for a in expr.args)})"
    val = getattr(expr, "value", None)
    return str(val) if val is not None else f"<{type(expr).__name__}>"


def _fmt(iv: Interval) -> str:
    if iv.lo is None and iv.hi is None:
        return "TOP"
    if iv.is_bot():
        return "BOT"
    lo = "-inf" if iv.lo is None else str(iv.lo)
    hi = "+inf" if iv.hi is None else str(iv.hi)
    return f"[{lo}, {hi}]"


__all__ = [
    "DefSite",
    "RefinementSite",
    "VarExplanation",
    "explain_var",
    "format_var_explanation",
]


# Re-exported on a Havoc class only for type completeness in callers
# that walk cmd_kind strings. Keeping import path short.
_ = AssignHavocCmd
