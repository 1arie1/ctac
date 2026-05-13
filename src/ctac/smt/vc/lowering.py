from __future__ import annotations

from collections import OrderedDict, defaultdict
from dataclasses import dataclass
import re
from typing import Any

from ctac.smt.vc.config import FactKind
from ctac.smt.vc.script import Assertion
from ctac.smt.vc.terms import Bool, Term, and_, eq, implies, not_, true


@dataclass(frozen=True)
class LeinoEdge:
    source: str
    target: str
    condition: Term
    premises: tuple[Term, ...] = ()


@dataclass(frozen=True)
class LeinoLowerer:
    entry_block: str
    edges: tuple[LeinoEdge, ...] = ()
    premise_kinds: frozenset[FactKind] = frozenset(
        {FactKind.DEF, FactKind.ASSUME, FactKind.RANGE, FactKind.LEMMA}
    )
    consequent_kinds: frozenset[FactKind] = frozenset({FactKind.ASSERT})
    ok_prefix: str = "OK_"

    def lower(self, builder: Any) -> tuple[Assertion, ...]:
        block_order = self._block_order(builder)
        ok_by_block = {
            block: builder.const(self._ok_name(block), Bool) for block in block_order
        }
        facts_by_block: dict[str, list[Any]] = defaultdict(list)
        passthrough: list[Assertion] = []
        for fact in builder.facts:
            if fact.scope is None:
                passthrough.append(self._assertion_from_fact(fact))
            else:
                facts_by_block[fact.scope.name].append(fact)

        edges_by_source: dict[str, list[LeinoEdge]] = defaultdict(list)
        for edge in self.edges:
            edges_by_source[edge.source].append(edge)

        assertions = list(passthrough)
        for block in block_order:
            facts = facts_by_block.get(block, [])
            premises = [f.term for f in facts if f.kind in self.premise_kinds]
            consequents = [f.term for f in facts if f.kind in self.consequent_kinds]
            for edge in edges_by_source.get(block, ()):
                consequents.append(
                    implies(
                        self._edge_premise(edge),
                        ok_by_block[edge.target],
                    )
                )
            body = self._block_body(premises, consequents)
            assertions.append(
                Assertion(
                    eq(ok_by_block[block], body),
                    name=f"{self.ok_prefix}{block}_def",
                    origin="leino-ok",
                )
            )
        assertions.append(
            Assertion(
                not_(ok_by_block[self.entry_block]),
                name=f"{self.ok_prefix}{self.entry_block}_discharge",
                origin="leino-discharge",
            )
        )
        return tuple(assertions)

    def _block_order(self, builder: Any) -> tuple[str, ...]:
        blocks: OrderedDict[str, None] = OrderedDict()
        blocks[self.entry_block] = None
        for fact in builder.facts:
            if fact.scope is not None:
                blocks.setdefault(fact.scope.name, None)
        for edge in self.edges:
            blocks.setdefault(edge.source, None)
            blocks.setdefault(edge.target, None)
        return tuple(blocks)

    def _block_body(self, premises: list[Term], consequents: list[Term]) -> Term:
        consequent = and_(*consequents) if consequents else true()
        if not premises:
            return consequent
        return implies(and_(*premises), consequent)

    def _edge_premise(self, edge: LeinoEdge) -> Term:
        if edge.premises:
            return and_(edge.condition, *edge.premises)
        return edge.condition

    def _ok_name(self, block: str) -> str:
        return f"{self.ok_prefix}{_sanitize_name(block)}"

    def _assertion_from_fact(self, fact: Any) -> Assertion:
        return Assertion(
            fact.term,
            scope=fact.scope,
            name=fact.name,
            comment=fact.comment,
            origin=fact.origin,
        )


def _sanitize_name(raw: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", raw)
    if not out:
        return "_"
    if out[0].isdigit():
        return "_" + out
    return out
