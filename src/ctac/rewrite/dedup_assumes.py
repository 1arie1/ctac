"""Same-block assume hygiene: duplicates and resolution pairs.

The frontend's summary-output protocol emits the same fact several
times in one block, in two recurring shapes:

* **Duplicates** — the identical condition repeated verbatim, or with
  flipped comparison orientation (``assume R149 <= R123`` followed by
  ``assume R123 >= R149``) or differing only in DSA meta suffixes.
  Conditions are compared after canonicalizing meta suffixes and
  normalizing ``Ge``/``Gt`` to the ``Le``/``Lt`` orientation; later
  occurrences are dropped.

* **Resolution pairs** — guarded facts emitted for both guard
  polarities::

      assume !(B) || P
      assume B || P

  By resolution the pair is equivalent to the unconditional ``P``; the
  first assume of the pair is replaced by ``P`` and the second dropped.
  Guard negation is recognized for ``LNot(B)`` vs ``B`` and for
  comparison complements (``Lt`` vs ``Ge``, ``Le`` vs ``Gt``,
  flip-normalized first).

Soundness: a duplicate adds no constraint; a resolution pair and its
resolvent define the same set of states (``(!B | P) & (B | P) <=> P``).
Both directions hold, so the rewrite preserves the feasible set
exactly. rw-eq's walker certifies the result without special cases:
the kept resolvent and the original pair discharge each other's
rule-4/4b CHKs.

Scope guard: within a block, an entry is invalidated when a command
defines any symbol its condition reads — a later syntactic duplicate
of a condition over redefined symbols is a different fact.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.analysis.expr_walk import iter_expr_symbols
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, TacCmd, TacExpr
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.rules.common import canonical_expr
from ctac.rewrite.unparse import canonicalize_cmd

_ORIENT_FLIP = {"Ge": "Le", "Gt": "Lt"}
# After flip-normalization: !(a < b) == (b <= a), !(a <= b) == (b < a).
_CMP_COMPLEMENT = {"Lt": "Le", "Le": "Lt"}


@dataclass(frozen=True)
class DedupAssumesResult:
    program: TacProgram
    duplicates_dropped: int
    pairs_resolved: int


def _normalize(cond: TacExpr) -> TacExpr:
    """Meta-canonical form with Ge/Gt rewritten to flipped Le/Lt, so
    both orientations of one fact share a key. Recurses through
    boolean structure."""

    def walk(e: TacExpr) -> TacExpr:
        if not isinstance(e, ApplyExpr):
            return e
        args = tuple(walk(a) for a in e.args)
        if e.op in _ORIENT_FLIP and len(args) == 2:
            return ApplyExpr(_ORIENT_FLIP[e.op], (args[1], args[0]))
        return ApplyExpr(e.op, args)

    return walk(canonical_expr(cond))


def _negation_key(e: TacExpr) -> TacExpr:
    """The normalized form of ``!e``, for the guard shapes we
    recognize: LNot-wrapped terms (unwrapped), Lt/Le comparisons
    (complemented), anything else (wrapped in LNot)."""
    if isinstance(e, ApplyExpr) and e.op == "LNot" and len(e.args) == 1:
        return e.args[0]
    if (
        isinstance(e, ApplyExpr)
        and e.op in _CMP_COMPLEMENT
        and len(e.args) == 2
    ):
        return ApplyExpr(_CMP_COMPLEMENT[e.op], (e.args[1], e.args[0]))
    return ApplyExpr("LNot", (e,))


def _symbols(e: TacExpr) -> frozenset[str]:
    return frozenset(iter_expr_symbols(e, strip_var_suffixes=True))


def dedup_assumes(program: TacProgram) -> DedupAssumesResult:
    duplicates = 0
    resolved = 0
    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        # Both maps record (index, symbols-read) per key; entries die
        # when any read symbol is redefined.
        seen: dict[TacExpr, tuple[int, frozenset[str]]] = {}
        # (pivot-key, payload-key) -> (idx, symbols, original payload
        # subexpression). The original (non-normalized) payload is what
        # replaces the partner: rw-eq's resolution rule matches it
        # against the surviving pair member's LOr arm modulo meta
        # suffixes, which a normalized form would defeat.
        guarded: dict[
            tuple[TacExpr, TacExpr],
            tuple[int, frozenset[str], TacExpr],
        ] = {}
        drops: set[int] = set()
        replacements: dict[int, TacExpr] = {}

        for idx, cmd in enumerate(block.commands):
            lhs = getattr(cmd, "lhs", None)
            if lhs is not None:
                d = canonical_symbol(lhs)
                for store in (seen, guarded):
                    for k in [k for k, v in store.items() if d in v[1]]:
                        del store[k]
            if not isinstance(cmd, AssumeExpCmd):
                continue
            key = _normalize(cmd.condition)
            syms = _symbols(key)
            if key in seen:
                drops.add(idx)
                duplicates += 1
                continue
            seen[key] = (idx, syms)
            cond = cmd.condition
            if (
                isinstance(key, ApplyExpr)
                and key.op == "LOr"
                and len(key.args) == 2
                and isinstance(cond, ApplyExpr)
                and cond.op == "LOr"
                and len(cond.args) == 2
            ):
                a, b = key.args
                for (pivot, payload), orig_payload in (
                    ((a, b), cond.args[1]),
                    ((b, a), cond.args[0]),
                ):
                    partner = guarded.get((_negation_key(pivot), payload))
                    if partner is not None and partner[0] not in drops:
                        replacements[partner[0]] = partner[2]
                        drops.add(idx)
                        resolved += 1
                        break
                    guarded[(pivot, payload)] = (idx, syms, orig_payload)

        if not drops and not replacements:
            new_blocks.append(block)
            continue
        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            if idx in drops:
                continue
            if idx in replacements:
                assert isinstance(cmd, AssumeExpCmd)
                new_cmds.append(
                    canonicalize_cmd(
                        replace(cmd, condition=replacements[idx])
                    )
                )
                continue
            new_cmds.append(cmd)
        new_blocks.append(replace(block, commands=new_cmds))
    return DedupAssumesResult(
        program=TacProgram(blocks=new_blocks),
        duplicates_dropped=duplicates,
        pairs_resolved=resolved,
    )
