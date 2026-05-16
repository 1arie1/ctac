"""Operations on parsed Smt2Files.

All functions return a new Smt2File (or modify the existing one and mark
statements `dirty` so emit re-renders them via pp instead of source slice).

Currently implemented:
- `memory_abstract` — replace `(define-fun M_n ((idx Int)) Int <body>)`
  chain links with `(declare-fun M_n (Int) Int)`. The bytemap chains
  used in the alias-cover work.
- `strip_check_sat` — drop the last `(check-sat)` and anything after.
- `name_asserts` — wrap selected assert bodies with `(! ... :named NAME)`.
- `scan_uf_arguments` — collect symbolic terms appearing as arguments
  to UF applications matching a name pattern. Implements the alias-cover
  T-extraction.
- `append_assert` — append a raw `(assert ...)` clause before the first
  check-sat (or at the end).
"""
from __future__ import annotations

import re
from dataclasses import replace
from typing import Callable

from ctac.solver.smt2.lexer import TokenKind
from ctac.solver.smt2.parser import (
    Assert,
    CheckSat,
    DeclareConst,
    DeclareFun,
    DefineFun,
    Smt2File,
    Smt2Statement,
)
from ctac.solver.smt2.sexpr import Atom, List_, SexprNode


def memory_abstract(file: Smt2File,
                     name_pattern: re.Pattern = re.compile(r'^M\w+$'),
                     ) -> Smt2File:
    """Replace each `(define-fun M_n ((idx Int)) Int <body>)` chain link
    matching `name_pattern` with `(declare-fun M_n (Int) Int)`.

    The bytemap-chain shape: single Int parameter, Int return. This
    matches the chain links emitted by ctac's smt encoder. Names like
    `TCSE17` (CSE-output chain links) match too if the pattern allows;
    by default we only match `M*` since that's what we want for
    memory abstraction.

    Returns a new Smt2File with modified statements marked dirty so
    emit() re-renders them."""
    new_stmts: list[Smt2Statement] = []
    changed = False
    for stmt in file.statements:
        if isinstance(stmt, DefineFun) and \
           name_pattern.match(stmt.name) and \
           _is_int_to_int(stmt):
            # Replace with declare-fun
            new_stmts.append(DeclareFun(
                name=stmt.name,
                param_sorts=[_int_atom()],
                ret_sort_node=_int_atom(),
                span=stmt.span,
                dirty=True,
            ))
            changed = True
        else:
            new_stmts.append(stmt)
    if not changed:
        return file
    return replace(file, statements=new_stmts)


def _is_int_to_int(stmt: DefineFun) -> bool:
    """Does this define-fun have the (idx Int) → Int signature?"""
    if len(stmt.params) != 1:
        return False
    p = stmt.params[0]
    if not (isinstance(p.sort_node, Atom) and p.sort_node.text == 'Int'):
        return False
    rs = stmt.ret_sort_node
    if not (isinstance(rs, Atom) and rs.text == 'Int'):
        return False
    return True


def _int_atom() -> Atom:
    return Atom(text='Int', kind=TokenKind.SYMBOL, span=(-1, -1))


def strip_check_sat(file: Smt2File) -> Smt2File:
    """Remove the last `(check-sat)` statement and everything after it.

    Useful when chaining transformations — re-appending check-sat after
    inserting new asserts is cleaner than stripping by regex."""
    last_idx: int | None = None
    for i, stmt in enumerate(file.statements):
        if isinstance(stmt, CheckSat):
            last_idx = i
    if last_idx is None:
        return file
    new_stmts = list(file.statements[:last_idx])
    return replace(file, statements=new_stmts)


def name_asserts(file: Smt2File,
                  picker: Callable[[Assert, int], str | None],
                  ) -> tuple[Smt2File, dict[str, Assert]]:
    """For each Assert returning a non-None name from picker(stmt, idx),
    wrap its body in `(! body :named NAME)`.

    Returns (new_file, name → Assert index) so callers can map an
    unsat-core back to the originating asserts.
    """
    index: dict[str, Assert] = {}
    new_stmts: list[Smt2Statement] = []
    changed = False
    assert_idx = 0
    for stmt in file.statements:
        if isinstance(stmt, Assert):
            name = picker(stmt, assert_idx)
            assert_idx += 1
            if name is not None:
                new_stmt = Assert(body=stmt.body, named=name,
                                   span=stmt.span, dirty=True)
                index[name] = new_stmt
                new_stmts.append(new_stmt)
                changed = True
                continue
        new_stmts.append(stmt)
    if not changed:
        return file, index
    return replace(file, statements=new_stmts), index


def scan_uf_arguments(file: Smt2File,
                       uf_name_pattern: re.Pattern,
                       *, declared_only: bool = True,
                       symbol_only: bool = True,
                       ) -> dict[str, list[str]]:
    """Collect terms appearing as arguments to UF applications.

    Walks every Assert body and every DefineFun body, looking for forms
    `(M_n <args...>)` where `M_n` matches `uf_name_pattern`. Collects
    each symbolic argument once per UF name.

    Args:
      uf_name_pattern: e.g. `re.compile(r'^M\\w+$')`.
      declared_only:   if True (default), filter args to symbols that
                       are introduced by `declare-const` / `declare-fun`
                       (excludes defined-fun derived constants like
                       `POW2_34_PLUS_40`).
      symbol_only:     if True (default), keep only Atom-kind SYMBOL
                       arguments (drops numerals and compound exprs).

    Returns a dict `{M_name: [arg_text, ...]}` with dedup-preserved order.
    """
    declared: set[str] = set()
    if declared_only:
        for s in file.statements:
            if isinstance(s, DeclareConst):
                declared.add(s.name)
            elif isinstance(s, DeclareFun):
                declared.add(s.name)

    found: dict[str, list[str]] = {}
    seen: dict[str, set[str]] = {}

    def emit(uf: str, arg: str) -> None:
        s = seen.setdefault(uf, set())
        if arg in s:
            return
        s.add(arg)
        found.setdefault(uf, []).append(arg)

    def visit(node: SexprNode) -> None:
        if isinstance(node, List_):
            # Is this a UF application?
            if node.children:
                h = node.children[0]
                if isinstance(h, Atom) and uf_name_pattern.match(h.text):
                    for arg in node.children[1:]:
                        if not isinstance(arg, Atom):
                            if not symbol_only:
                                emit(h.text, _atom_text(arg))
                            continue
                        if arg.kind is not TokenKind.SYMBOL:
                            if not symbol_only:
                                emit(h.text, arg.text)
                            continue
                        if declared_only and arg.text not in declared:
                            continue
                        emit(h.text, arg.text)
            for c in node.children:
                visit(c)

    # Walk statement bodies (skip define-fun M chain bodies' INTERNAL
    # recursive refs by ignoring chain-link define-funs themselves when
    # they match the pattern? No — we WANT to walk ALL bodies and find
    # UF args used at the user level. Internal (M_{n-1} idx) references
    # inside a chain link's body should be excluded though, since `idx`
    # is a bound variable. We approximate by skipping define-funs whose
    # param name appears as the arg — see filter below.)
    for s in file.statements:
        if isinstance(s, Assert):
            visit(s.body)
        elif isinstance(s, DefineFun):
            # If this is a chain-link define-fun (single Int param), skip
            # its body entirely — every (M_{n-1} idx) reference there is
            # an internal chain reference, not a user-level read.
            if _is_int_to_int(s):
                continue
            visit(s.body)

    return found


def _atom_text(node: SexprNode) -> str:
    """Best-effort source text for a non-Atom node (compound expression)."""
    if isinstance(node, Atom):
        return node.text
    if isinstance(node, List_):
        # Reconstruct a compact form for reporting purposes
        from ctac.solver.smt2.pp import pp_sexpr, PpPolicy
        from ctac.solver.smt2.doc import render
        return render(pp_sexpr(node, PpPolicy(width=10**9)), width=10**9)
    return str(node)


def append_assert(file: Smt2File, body_text: str,
                   *, named: str | None = None) -> Smt2File:
    """Append a `(assert <body>)` (optionally `(! <body> :named NAME)`)
    before the first check-sat / check-sat-using; or at the end if neither
    exists.

    `body_text` is parsed via the lexer + sexpr to ensure validity."""
    from ctac.solver.smt2 import parse as _parse
    if named is not None:
        src = f'(assert (! {body_text} :named {named}))\n'
    else:
        src = f'(assert {body_text})\n'
    f = _parse(src)
    if len(f.statements) != 1 or not isinstance(f.statements[0], Assert):
        raise ValueError(f'failed to parse appended assert: {body_text!r}')
    new_stmt = f.statements[0]
    new_stmt.dirty = True

    new_stmts = list(file.statements)
    # Find first CheckSat or CheckSatUsing
    insert_at = len(new_stmts)
    for i, s in enumerate(new_stmts):
        if isinstance(s, (CheckSat,)) or type(s).__name__ == 'CheckSatUsing':
            insert_at = i
            break
    new_stmts.insert(insert_at, new_stmt)
    return replace(file, statements=new_stmts)
