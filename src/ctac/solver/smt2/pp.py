"""Pretty-print Smt2File (and its sub-nodes) via the Doc algebra.

Layout policy is captured in `PpPolicy`:

- `width`               — soft target line width.
- `splitting_heads`     — heads (like `and`, `or`, `=>`, `ite`) whose
                           args go one-per-line when broken.
- `indent`              — extra indent applied to broken-form args.
- `show_comments`       — emit `;` comment blocks (default True).

Public entry points:
- `pp_sexpr(node, policy)` — single S-expr to a Doc.
- `pp_statement(stmt, policy)` — single Smt2Statement to a Doc.
- `pp_file(file, policy)` — full Smt2File to a Doc.
- `pp(file, policy)` — convenience: pp_file + render to string.
"""
from __future__ import annotations

from dataclasses import dataclass

from ctac.solver.smt2.doc import (
    Doc,
    align,
    concat,
    group,
    hardline,
    hsep,
    line,
    nest,
    parens,
    render,
    text,
)
from ctac.solver.smt2.parser import (
    Apply,
    Assert,
    CheckSat,
    CheckSatUsing,
    Comment,
    DeclareConst,
    DeclareFun,
    DefineFun,
    Exit,
    GetInfo,
    GetModel,
    GetUnsatCore,
    GetValue,
    Pop,
    Push,
    Raw,
    SetLogic,
    SetOption,
    Smt2File,
    Smt2Statement,
)
from ctac.solver.smt2.sexpr import Atom, CommentBlock, List_, SexprNode


# Heads whose argument list breaks one-per-line when the form is too wide.
_DEFAULT_SPLITTING_HEADS = frozenset({
    'and', 'or', '=>', 'ite',
    # Useful for our corpus:
    'let', 'forall', 'exists',
})


@dataclass
class PpPolicy:
    width: int = 100
    splitting_heads: frozenset[str] = _DEFAULT_SPLITTING_HEADS
    indent: int = 2                # extra nesting for broken-form args
    show_comments: bool = True


# ---- Sexpr → Doc -----------------------------------------------------------


def pp_sexpr(node: SexprNode, policy: PpPolicy = PpPolicy()) -> Doc:
    """Render a raw S-expr node to a Doc."""
    if isinstance(node, Atom):
        return text(node.text)
    if isinstance(node, CommentBlock):
        # Comments emit as their lines, each on a hardline so they always break.
        parts: list[Doc] = []
        for i, line_text in enumerate(node.lines):
            if i:
                parts.append(hardline())
            parts.append(text(line_text))
        return concat(parts)
    if isinstance(node, List_):
        return _pp_list(node, policy)
    return text(str(node))   # fallback — shouldn't happen


def _pp_list(node: List_, policy: PpPolicy) -> Doc:
    """Render a `(...)` form.

    Empty: `()`. With a head, the layout is:
      flat:    (head a b c)
      broken:  (head
                 a
                 b
                 c)

    For heads in `splitting_heads`, the broken layout is always chosen
    over the flat one when it fits — these forms (and/or/=>/ite) are
    clearer when args go one-per-line.
    """
    if not node.children:
        return text('()')
    head = node.children[0]
    rest = node.children[1:]

    head_doc = pp_sexpr(head, policy)
    if not rest:
        return parens(head_doc)

    rest_docs = [pp_sexpr(c, policy) for c in rest]

    # Compose argument body. `aligned_body` puts args one-per-line under
    # the column right after `(head ` when the group breaks.
    head_text_str = head.text if isinstance(head, Atom) else None
    forces_break = head_text_str in policy.splitting_heads

    # Argument list rendered horizontally with soft line breaks
    sep = line()
    args_doc = hsep(rest_docs, sep=sep)
    # Layout: (head <args>)
    body = concat([head_doc, text(' '), align(args_doc)])
    grouped = parens(body)
    if forces_break:
        # Don't try flat — always break for these heads when args are nontrivial
        # (but if all rest_docs together fit easily, group() still flattens).
        return group(grouped)
    return group(grouped)


# ---- Statement → Doc -------------------------------------------------------


def pp_statement(stmt: Smt2Statement, policy: PpPolicy = PpPolicy()) -> Doc:
    """Render a typed Smt2Statement to a Doc."""
    if isinstance(stmt, Comment):
        if not policy.show_comments:
            return text('')
        parts: list[Doc] = []
        for i, ln in enumerate(stmt.lines):
            if i:
                parts.append(hardline())
            parts.append(text(ln))
        return concat(parts)

    if isinstance(stmt, SetLogic):
        return text(f'(set-logic {stmt.logic})')
    if isinstance(stmt, SetOption):
        return concat([
            text('(set-option '), text(stmt.key), text(' '),
            pp_sexpr(stmt.value_node, policy), text(')'),
        ])
    if isinstance(stmt, DeclareConst):
        return concat([
            text(f'(declare-const {stmt.name} '),
            pp_sexpr(stmt.sort_node, policy), text(')'),
        ])
    if isinstance(stmt, DeclareFun):
        params_doc = parens(hsep(
            [pp_sexpr(p, policy) for p in stmt.param_sorts]))
        return concat([
            text(f'(declare-fun {stmt.name} '), params_doc, text(' '),
            pp_sexpr(stmt.ret_sort_node, policy), text(')'),
        ])
    if isinstance(stmt, DefineFun):
        param_docs: list[Doc] = []
        for p in stmt.params:
            param_docs.append(parens(concat([
                text(p.name), text(' '), pp_sexpr(p.sort_node, policy),
            ])))
        params_doc = parens(hsep(param_docs))
        body_doc = pp_sexpr(stmt.body, policy)
        return group(concat([
            text(f'(define-fun {stmt.name} '), params_doc, text(' '),
            pp_sexpr(stmt.ret_sort_node, policy),
            nest(policy.indent, concat([line(), body_doc])),
            text(')'),
        ]))
    if isinstance(stmt, Assert):
        inner_body = pp_sexpr(stmt.body, policy)
        if stmt.named is not None:
            # (assert (! BODY :named NAME))
            inner = concat([
                text('(! '), inner_body, text(f' :named {stmt.named})'),
            ])
        else:
            inner = inner_body
        return group(concat([
            text('(assert '),
            align(inner),
            text(')'),
        ]))
    if isinstance(stmt, CheckSat):
        return text('(check-sat)')
    if isinstance(stmt, CheckSatUsing):
        return concat([
            text('(check-sat-using '),
            pp_sexpr(stmt.tactic_node, policy), text(')'),
        ])
    if isinstance(stmt, Apply):
        return concat([
            text('(apply '),
            pp_sexpr(stmt.tactic_node, policy), text(')'),
        ])
    if isinstance(stmt, GetModel):
        return text('(get-model)')
    if isinstance(stmt, GetInfo):
        return text(f'(get-info {stmt.info_keyword})')
    if isinstance(stmt, GetValue):
        args_doc = parens(hsep([pp_sexpr(a, policy) for a in stmt.args]))
        return concat([text('(get-value '), args_doc, text(')')])
    if isinstance(stmt, GetUnsatCore):
        return text('(get-unsat-core)')
    if isinstance(stmt, Push):
        return text(f'(push {stmt.n})' if stmt.n != 1 else '(push)')
    if isinstance(stmt, Pop):
        return text(f'(pop {stmt.n})' if stmt.n != 1 else '(pop)')
    if isinstance(stmt, Exit):
        return text('(exit)')
    if isinstance(stmt, Raw):
        return pp_sexpr(stmt.node, policy)
    return text(f'<unknown stmt: {type(stmt).__name__}>')


# ---- File → Doc / string ---------------------------------------------------


def pp_file(file: Smt2File, policy: PpPolicy = PpPolicy()) -> Doc:
    parts: list[Doc] = []
    for i, stmt in enumerate(file.statements):
        if i:
            parts.append(hardline())
        parts.append(pp_statement(stmt, policy))
    return concat(parts)


def pp(file: Smt2File, policy: PpPolicy = PpPolicy()) -> str:
    """Convenience: render an Smt2File to a string."""
    return render(pp_file(file, policy), width=policy.width) + '\n'
