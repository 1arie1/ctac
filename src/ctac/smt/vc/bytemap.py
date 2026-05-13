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
            self.vc.fact(
                FactKind.RANGE,
                self.vc.bv_range(256, result),
                scope=None,
                name=f"bytemap_select_range_{site.id}",
                origin="bytemap-select-range",
            )
