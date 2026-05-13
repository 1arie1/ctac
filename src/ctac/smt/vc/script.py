from __future__ import annotations

from dataclasses import dataclass, field

from ctac.smt.vc.terms import Sort, Term, implies


@dataclass(frozen=True)
class ConstDecl:
    name: str
    sort: Sort


@dataclass(frozen=True)
class FunDecl:
    name: str
    args: tuple[Sort, ...]
    ret: Sort


@dataclass(frozen=True)
class DefineFun:
    name: str
    params: tuple[tuple[str, Sort], ...]
    ret: Sort
    body: Term


@dataclass(frozen=True)
class Scope:
    name: str
    guard: Term


@dataclass(frozen=True)
class Assertion:
    term: Term | None
    scope: Scope | None = None
    name: str | None = None
    comment: str | None = None
    origin: str | None = None
    block: str | None = None

    def scoped_term(self) -> Term:
        if self.term is None:
            raise ValueError("comment-only assertion has no scoped term")
        if self.scope is None:
            return self.term
        return implies(self.scope.guard, self.term)


@dataclass(frozen=True)
class VCScript:
    logic: str
    const_decls: tuple[ConstDecl, ...] = field(default_factory=tuple)
    fun_decls: tuple[FunDecl, ...] = field(default_factory=tuple)
    define_funs: tuple[DefineFun, ...] = field(default_factory=tuple)
    lemma_defs: tuple[DefineFun, ...] = field(default_factory=tuple)
    assertions: tuple[Assertion, ...] = field(default_factory=tuple)
    comments: tuple[str, ...] = field(default_factory=tuple)
    produce_models: bool = False
    produce_unsat_cores: bool = False
    check_sat: bool = True
    warnings: tuple[str, ...] = field(default_factory=tuple)


class SmtWriter:
    def __init__(self) -> None:
        self.lines: list[str] = []
        self.indent = 0

    def line(self, text: str = "") -> None:
        self.lines.append(("  " * self.indent) + text)

    def comment(self, text: str) -> None:
        for line in text.splitlines() or [""]:
            self.line(f"; {line}")

    def emit(self) -> str:
        return "\n".join(self.lines) + "\n"


def _emit_define_fun(w: SmtWriter, df: DefineFun) -> None:
    params = " ".join(f"({name} {sort.smt()})" for name, sort in df.params)
    w.line(f"(define-fun {df.name} ({params}) {df.ret.smt()} {df.body.smt()})")


def _emit_assertion(w: SmtWriter, assertion: Assertion, *, name_assertions: bool) -> None:
    if assertion.comment:
        w.comment(assertion.comment)
    if assertion.term is None:
        return
    body = assertion.scoped_term().smt()
    if name_assertions and assertion.name:
        w.line(f"(assert (! {body} :named {assertion.name}))")
    else:
        w.line(f"(assert {body})")


def render_vc_script(script: VCScript) -> str:
    w = SmtWriter()
    if script.produce_models:
        w.line("(set-option :produce-models true)")
    if script.produce_unsat_cores:
        w.line("(set-option :produce-unsat-cores true)")
    for comment in script.comments:
        w.comment(comment)
    w.line(f"(set-logic {script.logic})")
    if script.const_decls or script.fun_decls:
        w.line()
    for decl in script.const_decls:
        w.line(f"(declare-const {decl.name} {decl.sort.smt()})")
    for decl in script.fun_decls:
        args = " ".join(sort.smt() for sort in decl.args)
        w.line(f"(declare-fun {decl.name} ({args}) {decl.ret.smt()})")
    if script.define_funs:
        w.line()
        for df in script.define_funs:
            _emit_define_fun(w, df)
    if script.lemma_defs:
        w.line()
        for lemma in script.lemma_defs:
            _emit_define_fun(w, lemma)
    if script.assertions:
        w.line()
        last_block: str | None = None
        for assertion in script.assertions:
            if assertion.term is None:
                if w.lines and w.lines[-1] != "":
                    w.line()
                _emit_assertion(
                    w,
                    assertion,
                    name_assertions=script.produce_unsat_cores,
                )
                last_block = None
                continue
            if assertion.block is not None and assertion.block != last_block:
                if w.lines and w.lines[-1] != "":
                    w.line()
                w.comment(f"block {assertion.block}")
                last_block = assertion.block
            _emit_assertion(
                w,
                assertion,
                name_assertions=script.produce_unsat_cores,
            )
    if script.check_sat:
        w.line()
        w.line("(check-sat)")
        if script.produce_models:
            w.line("(get-model)")
        if script.produce_unsat_cores:
            w.line("(get-unsat-core)")
    return w.emit()
