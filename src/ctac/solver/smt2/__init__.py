"""ctac.solver.smt2 — SMT-LIB v2 parser, AST, pretty-printer, and ops.

A two-tier parser:

- Tier 1 (sexpr): position-aware tokenizer + raw S-expr parser. Nodes
  carry source spans so unchanged forms round-trip byte-identical.
- Tier 2 (parser): command-level dispatch over top-level forms into
  typed `Smt2Statement` variants. Bodies stay as raw S-expr nodes — we
  have no `let` / quantifiers, so the raw S-expr representation IS the
  expression representation.

Operations on parsed files live in `ops.py`. Pretty-printing is in
`pp.py` (built on a Wadler-style Doc algebra in `doc.py`).
"""
from __future__ import annotations

from ctac.solver.smt2.lexer import (
    Token,
    TokenKind,
    Smt2LexError,
    tokenize,
)
from ctac.solver.smt2.sexpr import (
    SexprNode,
    Atom,
    List_,
    CommentBlock,
    Smt2ParseError,
    parse_sexprs,
)
from ctac.solver.smt2.parser import (
    Smt2File,
    Smt2Statement,
    SetOption,
    SetLogic,
    DeclareConst,
    DeclareFun,
    DefineFun,
    DefineFunParam,
    Assert,
    CheckSat,
    CheckSatUsing,
    Apply,
    GetModel,
    GetInfo,
    GetValue,
    GetUnsatCore,
    Push,
    Pop,
    Exit,
    Comment,
    Raw,
    parse,
)
from ctac.solver.smt2.emit import emit
from ctac.solver.smt2.pp import pp, pp_file, pp_statement, pp_sexpr, PpPolicy
from ctac.solver.smt2.ops import (
    memory_abstract,
    strip_check_sat,
    name_asserts,
    scan_uf_arguments,
    append_assert,
)

__all__ = [
    # lexer
    'Token', 'TokenKind', 'Smt2LexError', 'tokenize',
    # sexpr
    'SexprNode', 'Atom', 'List_', 'CommentBlock',
    'Smt2ParseError', 'parse_sexprs',
    # parser (commands)
    'Smt2File', 'Smt2Statement',
    'SetOption', 'SetLogic', 'DeclareConst', 'DeclareFun',
    'DefineFun', 'DefineFunParam',
    'Assert', 'CheckSat', 'CheckSatUsing', 'Apply',
    'GetModel', 'GetInfo', 'GetValue', 'GetUnsatCore',
    'Push', 'Pop', 'Exit', 'Comment', 'Raw',
    'parse',
    # emit
    'emit',
    # pp
    'pp', 'pp_file', 'pp_statement', 'pp_sexpr', 'PpPolicy',
    # ops
    'memory_abstract', 'strip_check_sat', 'name_asserts',
    'scan_uf_arguments', 'append_assert',
]
