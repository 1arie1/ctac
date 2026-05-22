"""Propagate ``X = SymbolRef(Y)`` aliases into AnnotationCmd payloads.

When ``CP_ALIAS`` or another rewrite identifies ``X`` as an alias for
``Y`` (i.e. ``X``'s unique static def is ``AssignExpCmd X SymbolRef(Y)``),
CP propagates the alias into *expression* operands — every use of ``X``
in an Eq, Add, Ite condition, etc. becomes ``Y``. After CP fires on all
operand uses, DCE removes ``X``'s defining assignment.

But CP doesn't reach AnnotationCmd payloads. Those carry JSON metadata
(``snippet.cmd`` for cex prints, ``sbf.inline.end`` for trace marker
function-return values) that reference symbols *by name string*. The
parser surfaces those name references as :attr:`AnnotationCmd.weak_refs`
— deliberately weak so DCE can still eliminate the underlying defs. The
net effect: after CP + DCE, ``X`` is gone from the program but the
AnnotationCmd still names it as the symbol-of-interest; the cex printer
then resolves ``X`` against a now-undefined variable.

This pass closes the gap. For every AnnotationCmd whose ``weak_refs``
contain a name ``X`` whose static def is ``X = SymbolRef(Y)``, we
rewrite the JSON payload's symbol-position fields and the ``weak_refs``
tuple from ``X`` to the alias-chain-resolved target.

Constant aliases (``X = ConstExpr(c)``) are *not* propagated — the
annotation's symbol-position fields name symbols, not literals; there's
no faithful substitution. ``X``'s def is left untouched in that case
so DCE preserves it (the strong-ref-via-payload-symbol keeps the def
alive). This is rare in practice; the common shape is symbol-to-symbol
aliasing produced by Ite collapses.
"""

from __future__ import annotations

import json
from dataclasses import replace

from ctac.ast.nodes import (
    AnnotationCmd,
    AssignExpCmd,
    SymbolRef,
    SymbolWeakRef,
    TacCmd,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd


def _build_alias_map(program: TacProgram) -> dict[str, str]:
    """Symbol -> alias-target name, restricted to SymbolRef RHSes with a
    unique definition. Transitive closure applied lazily by :func:`_resolve`.

    Ignores multi-def symbols (DSA-dynamic): an annotation referencing a
    dynamic should keep naming the dynamic, since each definition's RHS
    may point at a different alias target.
    """
    defs: dict[str, list[SymbolRef]] = {}
    for block in program.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd) and isinstance(cmd.rhs, SymbolRef):
                defs.setdefault(cmd.lhs, []).append(cmd.rhs)
    return {
        lhs: rhs[0].name
        for lhs, rhs in defs.items()
        if len(rhs) == 1
    }


def _resolve(name: str, alias: dict[str, str]) -> str:
    """Walk the alias chain to a fixed point; abort on cycles (shouldn't
    happen in DSA but cheap to defend)."""
    seen = {name}
    current = name
    while current in alias:
        nxt = alias[current]
        if nxt in seen:
            return current
        seen.add(nxt)
        current = nxt
    return current


def _substitute_in_payload(
    payload: str, subs: dict[str, str]
) -> tuple[str, int]:
    """JSON-aware substitution: re-serialize the payload with every
    string value matching a key in ``subs`` replaced by its target.

    Symbol-position fields use the same key-set the parser excludes from
    name extraction — ``#class`` / ``displayMessage`` / ``scopeName`` /
    ``name`` / ``namePrefixType`` are *not* symbol positions and are
    left alone. The substitution is anchored on field key, not on
    value-shape, so a symbol name that happens to collide with a
    display string is safe.

    Returns ``(possibly_new_payload, substitution_count)``. When the
    payload doesn't parse as JSON or no substitution applies, returns
    the original string unchanged and ``0``.
    """
    if not payload.strip().startswith("JSON"):
        return payload, 0
    try:
        obj = json.loads(payload.strip()[4:])
    except json.JSONDecodeError:
        return payload, 0

    skip_keys = {"#class", "displayMessage", "scopeName", "name", "namePrefixType"}
    count = 0

    def walk(node: object, parent_key: str | None) -> object:
        nonlocal count
        if isinstance(node, dict):
            return {k: walk(v, parent_key=k) for k, v in node.items()}
        if isinstance(node, list):
            return [walk(v, parent_key=parent_key) for v in node]
        if isinstance(node, str) and parent_key not in skip_keys and node in subs:
            count += 1
            return subs[node]
        return node

    new_obj = walk(obj, parent_key=None)
    if count == 0:
        return payload, 0
    # Compact JSON to match the prover's typical single-line serialization.
    return "JSON" + json.dumps(new_obj, separators=(",", ":")), count


def propagate_aliases_into_annotations(
    program: TacProgram,
) -> tuple[TacProgram, int]:
    """Rewrite every AnnotationCmd's payload symbol-position fields
    and ``weak_refs`` tuple from each aliased name to its
    chain-resolved target.

    Alias source: ``AssignExpCmd X SymbolRef(Y)`` static defs in
    ``program``. CP_ALIAS / IteZeroOrSelf turn an Ite-fold into
    ``Rnew = Rold`` and propagate the rename into operand uses; this
    pass closes the loop on the annotation refs that CP can't reach.

    The full alias map is passed to every annotation (not just those
    whose extracted ``weak_refs`` happen to name the symbol) — only
    ``snippet.cmd`` annotations have weak_refs surfaced today, but
    ``sbf.inline.end`` (the call-site retVal trace) and other JSON
    shapes reference symbols by ``namePrefix`` too. Substituting
    against the full alias map keeps these in sync.

    Returns the (possibly-new) program and the count of individual
    symbol substitutions made across all annotations.
    """
    alias = _build_alias_map(program)
    if not alias:
        return program, 0

    # Resolve transitive aliases once.
    resolved: dict[str, str] = {
        name: _resolve(name, alias) for name in alias
    }
    resolved = {k: v for k, v in resolved.items() if k != v}
    if not resolved:
        return program, 0

    total_subs = 0
    new_blocks: list[TacBlock] = []
    program_changed = False
    for block in program.blocks:
        new_cmds: list[TacCmd] = []
        block_changed = False
        for cmd in block.commands:
            if not isinstance(cmd, AnnotationCmd):
                new_cmds.append(cmd)
                continue
            new_payload, payload_subs = _substitute_in_payload(
                cmd.payload, resolved
            )
            new_weak_refs = tuple(
                SymbolWeakRef(resolved.get(ref.name, ref.name))
                for ref in cmd.weak_refs
            )
            weak_changed = new_weak_refs != cmd.weak_refs
            if payload_subs == 0 and not weak_changed:
                new_cmds.append(cmd)
                continue
            # Re-canonicalize ``raw`` so render_program emits the
            # substituted payload (render writes cmd.raw verbatim).
            new_cmd = canonicalize_cmd(
                replace(cmd, payload=new_payload, weak_refs=new_weak_refs)
            )
            new_cmds.append(new_cmd)
            total_subs += payload_subs
            block_changed = True
        if block_changed:
            new_blocks.append(replace(block, commands=new_cmds))
            program_changed = True
        else:
            new_blocks.append(block)
    if not program_changed:
        return program, 0
    return replace(program, blocks=new_blocks), total_subs
