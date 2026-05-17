from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable

from ctac.smt.vc.config import BytemapConfig, FactKind
from ctac.smt.vc.terms import Int, Term, app, eq, term

_MAP_PARAM = "idx"


@dataclass(frozen=True)
class MapTerm:
    name: str

    def smt(self) -> str:
        return self.name


@dataclass
class SelectSite:
    id: int
    map: MapTerm
    index: Term
    raw_result: Term
    bound_result: Term | None = None
    scope: Any = None
    """Scope at the call site — recorded so the per-application
    range axiom can be guarded per rule 4 (default scoped) and
    rule 7 (relaxed to global when the result is bound to a
    scoped-def LHS). Bytemap Select intentionally lives outside
    the `Ops` / `LemmaSchema` machinery — we want freedom to
    explore minimizing memory axiom instantiations — so its rule
    4/5/7 routing is handled directly in `finalize`."""
    bound_def_scoped: bool = False
    """Rule 7 flag. `BlockBuilder._bind_direct_result` sets this
    when this Select's bound_result is the LHS of a scoped (block-
    guarded) static def. Then the range axiom can stay global:
    when the block is bypassed the LHS is free, the range is
    trivially satisfied, and no constraint propagates onto shared
    bytemap values."""

    def result_for_range(self) -> Term:
        return self.bound_result or self.raw_result


class UfDefineFunBytemap:
    def __init__(self, vc: Any, config: BytemapConfig) -> None:
        self.vc = vc
        self.config = config
        self.select_sites: list[SelectSite] = []

    def ref(self, name: str) -> MapTerm:
        return MapTerm(name)

    def havoc(self, name: str) -> MapTerm:
        self.vc.declare_fun(name, (Int,), Int)
        return MapTerm(name)

    def define(self, name: str, body: Callable[[Term], Term]) -> MapTerm:
        param = term(_MAP_PARAM, Int)
        self.vc.define_fun(name, ((_MAP_PARAM, Int),), Int, body(param))
        return MapTerm(name)

    def store(self, name: str, base: MapTerm, index: Term, value: Term) -> MapTerm:
        return self.define(
            name,
            lambda param: app(
                "ite",
                [
                    eq(param, index),
                    value,
                    app(base.name, [param], Int),
                ],
                Int,
            ),
        )

    def select(self, map_term: MapTerm, index: Term) -> Term:
        raw = app(map_term.name, [index], Int)
        site = SelectSite(
            id=len(self.select_sites),
            map=map_term,
            index=index,
            raw_result=raw,
            scope=self.vc.current_scope(),
        )
        self.select_sites.append(site)
        return Term(
            raw.text,
            raw.sort,
            callsites=raw.callsites,
            direct_callsite=site,
        )

    def finalize(self) -> None:
        if self.config.select_range == "none":
            return
        if self.config.select_range != "binder":
            raise ValueError(f"unknown bytemap select_range {self.config.select_range!r}")
        for site in self.select_sites:
            result = site.result_for_range()
            # Rule 4: Select is partial (rule 8), so its range axiom
            # is scoped to the call's block by default. Rule 7: if
            # the Select's result is bound to the LHS of a scoped
            # def, the axiom can stay global — when the block is
            # bypassed the LHS is free and the range constraint is
            # trivially satisfied. This is the common pattern
            # `R := Select(M, idx)` and keeps loose bv256 bounds in
            # scope for NLA without unsoundness.
            #
            # --guard-axioms (the uniform-scoping mode) does NOT
            # override rule 7 here — same policy as the lemma path
            # in `generate_lemma_instances`. Partial axioms are
            # always conservative (scoped) except for the explicit
            # rule-7 relaxation.
            scope = None if site.bound_def_scoped else site.scope
            self.vc.fact(
                FactKind.RANGE,
                self.vc.bv_range(256, result),
                scope=scope,
                name=f"bytemap_select_range_{site.id}",
                origin="bytemap-select-range",
            )
