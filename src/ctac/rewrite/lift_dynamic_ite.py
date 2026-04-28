"""Lift dynamic-Ite-RHS assignments out of their host block.

When a block has multiple DSA-dynamic ``AssignExpCmd`` and at least
one of them carries an ``Ite`` on its RHS, we hoist the RHSs as a
contiguous block of fresh static defs *before* the first dynamic
assignment in that block. The original dynamic commands become bare
aliases of the new T-vars.

The lift exists to unblock :mod:`ctac.rewrite.rules.ite_purify`. That
rule introduces ``TB<N> = <cond>`` static defs at the use site of an
``Ite``; if the use sits in a block whose static prefix has already
ended (i.e., another dynamic assignment precedes it), the new TB
lands between two dynamics and breaks sea_vc's
``(static)*(dynamic)*term`` block-shape invariant. Lifting the
Ite-RHS dynamic into a static T at the top of the dynamic group
gives ITE_PURIFY a clean static neighborhood to insert into.

Transform (single block, two dynamics, ``y``'s RHS references ``x``)::

    x := u1
    y := u2

becomes::

    T1 := u1
    T2 := u2[x := T1]
    x := T1
    y := T2

The substitution ``[x := T1]`` is essential: ``T2`` is now defined
*before* ``x``, so any reference to ``x`` inside ``u2`` would be a
use-before-def. Since ``T1 = u1 = x``'s computed value, the
substitution preserves semantics.

Trigger condition: the block has ≥2 dynamic ``AssignExpCmd`` *and*
at least one of them has an ``Ite`` RHS. Single-dynamic blocks need
no lift (ITE_PURIFY has a clean prefix to insert into); blocks with
no Ite-RHS dynamic gain nothing from the lift.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.analysis.passes import analyze_dsa, extract_def_use
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd


@dataclass(frozen=True)
class LiftResult:
    program: TacProgram
    hits: int
    extra_symbols: tuple[tuple[str, str], ...]


def _substitute(expr: TacExpr, rename: dict[str, str]) -> TacExpr:
    """Replace ``SymbolRef(x)`` with ``SymbolRef(rename[x])`` recursively."""
    if not rename:
        return expr
    if isinstance(expr, SymbolRef):
        new_name = rename.get(expr.name)
        if new_name is None:
            return expr
        return SymbolRef(new_name)
    if isinstance(expr, ApplyExpr):
        # ``Apply(callee, ...)``: args[0] is a function tag, not a
        # program variable — don't rename it.
        new_args: list[TacExpr] = []
        any_changed = False
        for i, a in enumerate(expr.args):
            if expr.op == "Apply" and i == 0:
                new_args.append(a)
                continue
            new_a = _substitute(a, rename)
            if new_a is not a:
                any_changed = True
            new_args.append(new_a)
        if any_changed:
            return ApplyExpr(expr.op, tuple(new_args))
        return expr
    return expr


def lift_dynamic_ite_rhs(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> LiftResult:
    if not program.blocks:
        return LiftResult(program=program, hits=0, extra_symbols=())

    du = extract_def_use(program)
    dsa = analyze_dsa(program, def_use=du)
    dynamic_symbols = {a.symbol for a in dsa.dynamic_assignments}

    existing_names: set[str] = set(du.symbol_to_id)
    fresh_counter = 0

    def next_t_name() -> str:
        nonlocal fresh_counter
        while True:
            name = f"TDYN{fresh_counter}"
            fresh_counter += 1
            if name not in existing_names:
                existing_names.add(name)
                return name

    new_blocks: list[TacBlock] = []
    extra_symbols: list[tuple[str, str]] = []
    hits = 0

    for block in program.blocks:
        # Collect indices of dynamic ``AssignExpCmd`` in source order.
        dyn_indices: list[int] = []
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, AssignExpCmd) and cmd.lhs in dynamic_symbols:
                dyn_indices.append(idx)
        if len(dyn_indices) < 2:
            new_blocks.append(block)
            continue
        # Trigger only when at least one dynamic carries an Ite RHS —
        # otherwise the lift adds noise without unblocking anything.
        has_ite = any(
            isinstance(block.commands[i].rhs, ApplyExpr)
            and block.commands[i].rhs.op == "Ite"
            for i in dyn_indices
        )
        if not has_ite:
            new_blocks.append(block)
            continue

        first_dyn = dyn_indices[0]
        rename: dict[str, str] = {}
        t_defs: list[TacCmd] = []
        aliases: dict[int, TacCmd] = {}
        for idx in dyn_indices:
            cmd = block.commands[idx]
            assert isinstance(cmd, AssignExpCmd)
            t_name = next_t_name()
            sort = "bv256"
            if symbol_sorts is not None:
                sort = symbol_sorts.get(cmd.lhs, sort)
            extra_symbols.append((t_name, sort))
            new_rhs = _substitute(cmd.rhs, rename)
            t_defs.append(
                canonicalize_cmd(
                    AssignExpCmd(raw="", lhs=t_name, rhs=new_rhs)
                )
            )
            aliases[idx] = canonicalize_cmd(
                AssignExpCmd(raw="", lhs=cmd.lhs, rhs=SymbolRef(t_name))
            )
            rename[cmd.lhs] = t_name
            hits += 1

        new_cmds: list[TacCmd] = []
        for i, c in enumerate(block.commands):
            if i == first_dyn:
                new_cmds.extend(t_defs)
            new_cmds.append(aliases.get(i, c))
        new_blocks.append(replace(block, commands=new_cmds))

    return LiftResult(
        program=TacProgram(blocks=new_blocks),
        hits=hits,
        extra_symbols=tuple(extra_symbols),
    )


__all__ = ["LiftResult", "lift_dynamic_ite_rhs"]
