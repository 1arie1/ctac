"""Rewrite trail: substitutions recorded during destructive rewrites.

Some rewrite rules eliminate havoc'd variables by proving them equal to
another variable (the "survivor"). The variable disappears from the
program text and from the SMT encoded by `ctac smt`, so a solver model
has no entry for it. `ctac run --model` replaying the *original* `.tac`
then defaults the eliminated variable to a sentinel at its havoc cmd,
which the original's range-constraint assume rejects.

A trail records the per-rewrite substitution ``R -> replacement`` so
the replay can recover R's value from the surviving model variable.
For v1 the destructive rules that need a trail are
:mod:`~ctac.rewrite.rules.havoc_equate_subst` and
:mod:`~ctac.rewrite.rules.havoc_equate_fold` (the only rules that
eliminate *havoc'd* names; rules that eliminate ``AssignExpCmd`` defs
leave RHSes the interpreter can re-evaluate from the original program).

The on-disk format is a versioned JSON sidecar; loading a trail accepts
multiple rewrite steps concatenated and resolves chains transitively
(R -> X in step 1, X -> Y in step 2 yields R -> Y at lookup time).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef, TacExpr
from ctac.ast.parse_expr import parse_expr
from ctac.ir.models import TacProgram
from ctac.rewrite.unparse import unparse_expr


TRAIL_VERSION = 1


@dataclass(frozen=True)
class Substitution:
    """One ``var -> replacement`` substitution recorded by a rule."""

    var: str
    replacement: TacExpr
    rule: str


def _collect_program_symbols(program: TacProgram) -> set[str]:
    """Canonical names that appear anywhere in ``program``.

    A name in this set is declared by the SMT encoder and present in
    any SAT model, so trail entries pointing to it resolve directly.
    """
    names: set[str] = set()

    def walk_expr(e: TacExpr) -> None:
        if isinstance(e, SymbolRef):
            names.add(canonical_symbol(e.name))
        elif isinstance(e, ApplyExpr):
            for a in e.args:
                walk_expr(a)

    for block in program.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd):
                names.add(canonical_symbol(cmd.lhs))
                walk_expr(cmd.rhs)
            elif hasattr(cmd, "lhs"):
                names.add(canonical_symbol(cmd.lhs))
            elif hasattr(cmd, "condition") and isinstance(
                getattr(cmd, "condition", None), TacExpr
            ):
                walk_expr(cmd.condition)
            elif hasattr(cmd, "predicate") and isinstance(
                getattr(cmd, "predicate", None), TacExpr
            ):
                walk_expr(cmd.predicate)
            elif hasattr(cmd, "condition") and isinstance(
                getattr(cmd, "condition", None), str
            ):
                names.add(canonical_symbol(cmd.condition))
    return names


def _build_original_defs(program: TacProgram) -> dict[str, TacExpr]:
    """Map ``canonical_lhs -> rhs`` for every ``AssignExpCmd`` in
    ``program``. DSA-merged names with multiple defs are dropped (same
    reasoning as :func:`ctac.transform.pin._build_definition_map`)."""
    by_canon: dict[str, list[TacExpr]] = {}
    for block in program.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd):
                by_canon.setdefault(canonical_symbol(cmd.lhs), []).append(cmd.rhs)
    return {k: rhss[0] for k, rhss in by_canon.items() if len(rhss) == 1}


def _resolve_to_survivors(
    expr: TacExpr,
    original_defs: dict[str, TacExpr],
    survivors: set[str],
    seen: frozenset[str],
) -> TacExpr:
    """Inline non-survivor ``SymbolRef``s through ``original_defs`` so
    every leaf is a survivor (or a name with no original def, which we
    leave as-is). Cycle-safe via ``seen``."""
    if isinstance(expr, ConstExpr):
        return expr
    if isinstance(expr, SymbolRef):
        name = canonical_symbol(expr.name)
        if name in survivors:
            return SymbolRef(name)
        if name in seen:
            return SymbolRef(name)
        if name in original_defs:
            return _resolve_to_survivors(
                original_defs[name], original_defs, survivors, seen | {name}
            )
        return SymbolRef(name)
    if isinstance(expr, ApplyExpr):
        new_args = tuple(
            _resolve_to_survivors(a, original_defs, survivors, seen)
            for a in expr.args
        )
        return ApplyExpr(expr.op, new_args)
    return expr


def resolve_substitutions(
    raw: tuple[Substitution, ...],
    *,
    original_program: TacProgram,
    rewritten_program: TacProgram,
) -> tuple[Substitution, ...]:
    """Expand each substitution's target so its free variables are
    all *survivors* — names that appear in ``rewritten_program`` and
    therefore exist in the SMT model.

    When a rule recorded ``R -> X`` but ``X`` was later DCE'd (e.g.
    ``HavocEquateFold`` pointed at ``R309`` which then fell out via
    bitfield/div rewrites), ``X`` won't be in the model, and
    ``ev.get_symbol(X)`` at replay would default to the sentinel. By
    inlining ``X``'s ``AssignExpCmd`` RHS from the *original* program
    we land the trail entry on havoc'd survivors that the model does
    pin (e.g. ``narrow([2^32] *int R306) >> [2^5]``).
    """
    survivors = _collect_program_symbols(rewritten_program)
    original_defs = _build_original_defs(original_program)
    out: list[Substitution] = []
    for s in raw:
        resolved = _resolve_to_survivors(
            s.replacement, original_defs, survivors, frozenset()
        )
        out.append(Substitution(var=s.var, replacement=resolved, rule=s.rule))
    return tuple(out)


@dataclass(frozen=True)
class Trail:
    """An ordered, deduplicated set of substitutions.

    Lookup walks the chain transitively with a cycle guard, so trails
    composed from multiple rewrite steps (R -> X, then X -> Y) resolve
    to the final survivor.
    """

    substitutions: tuple[Substitution, ...] = field(default_factory=tuple)

    @classmethod
    def from_substitutions(cls, subs: tuple[Substitution, ...]) -> Trail:
        seen: set[str] = set()
        out: list[Substitution] = []
        for s in subs:
            key = canonical_symbol(s.var)
            if key in seen:
                continue
            seen.add(key)
            out.append(
                Substitution(var=key, replacement=s.replacement, rule=s.rule)
            )
        return cls(substitutions=tuple(out))

    def _by_var(self) -> dict[str, Substitution]:
        return {s.var: s for s in self.substitutions}

    def lookup(self, var: str) -> TacExpr | None:
        """Return the final replacement expression for ``var``, or ``None``.

        Transitively walks chains: if ``R -> X`` and ``X -> Y`` are both
        recorded, ``lookup("R") -> SymbolRef("Y")``. Cycles (which
        shouldn't arise but cheap to defend against) return ``None``.
        """
        table = self._by_var()
        key = canonical_symbol(var)
        if key not in table:
            return None
        seen: set[str] = set()
        current = key
        last_replacement: TacExpr | None = None
        while current in table:
            if current in seen:
                return None
            seen.add(current)
            last_replacement = table[current].replacement
            if isinstance(last_replacement, SymbolRef):
                current = canonical_symbol(last_replacement.name)
            else:
                break
        return last_replacement

    def merge(self, other: Trail) -> Trail:
        """Concatenate two trails (``self`` first, then ``other``).

        Used by project-mode auto-discovery to compose trails from
        multiple rewrite steps in HEAD's lineage. Earlier substitutions
        win on key collisions; transitive chains form across steps
        because :meth:`lookup` walks them at query time.
        """
        return Trail.from_substitutions(self.substitutions + other.substitutions)

    def to_json(self) -> str:
        payload = {
            "version": TRAIL_VERSION,
            "substitutions": [
                {
                    "var": s.var,
                    "replacement": unparse_expr(s.replacement),
                    "rule": s.rule,
                }
                for s in self.substitutions
            ],
        }
        return json.dumps(payload, indent=2) + "\n"

    @classmethod
    def from_json(cls, text: str) -> Trail:
        try:
            payload = json.loads(text)
        except json.JSONDecodeError as e:
            raise ValueError(f"trail is not valid JSON: {e}") from e
        if not isinstance(payload, dict):
            raise ValueError("trail JSON must be an object")
        version = payload.get("version")
        if version != TRAIL_VERSION:
            raise ValueError(
                f"unsupported trail version {version!r}; expected {TRAIL_VERSION}"
            )
        entries = payload.get("substitutions", [])
        if not isinstance(entries, list):
            raise ValueError("'substitutions' must be a list")
        subs: list[Substitution] = []
        for i, entry in enumerate(entries):
            if not isinstance(entry, dict):
                raise ValueError(f"substitution {i} must be an object")
            try:
                var = entry["var"]
                repl_text = entry["replacement"]
                rule = entry["rule"]
            except KeyError as e:
                raise ValueError(
                    f"substitution {i} missing key {e.args[0]!r}"
                ) from e
            replacement = parse_expr(repl_text)
            subs.append(
                Substitution(
                    var=canonical_symbol(var),
                    replacement=replacement,
                    rule=rule,
                )
            )
        return cls.from_substitutions(tuple(subs))
