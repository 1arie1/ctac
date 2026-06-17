"""Single-pass def-use analysis for Tiny TAC.

Mirrors ``ctac.analysis.defuse.extract_def_use``: one linear pass over
blocks and commands builds inverted indices (defs/uses per symbol) plus
per-block summaries, and assigns each definition a global ``def_id`` and
each symbol a compact ``symbol_id`` so reaching-definitions can run over
integer bitsets.
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterator
from dataclasses import dataclass, field

from ctac.ttac import ast


@dataclass(frozen=True)
class DefSite:
    symbol: str
    block: str
    cmd_index: int
    kind: str
    def_id: int
    symbol_id: int


@dataclass(frozen=True)
class UseSite:
    symbol: str
    block: str
    cmd_index: int
    kind: str


@dataclass(frozen=True)
class BlockDefUse:
    block: str
    def_sites: tuple[DefSite, ...]
    use_sites: tuple[UseSite, ...]

    @property
    def defs(self) -> frozenset[str]:
        return frozenset(d.symbol for d in self.def_sites)

    @property
    def uses(self) -> frozenset[str]:
        return frozenset(u.symbol for u in self.use_sites)


@dataclass(frozen=True)
class DefUse:
    by_block: dict[str, BlockDefUse]
    defs_by_symbol: dict[str, tuple[DefSite, ...]]
    uses_by_symbol: dict[str, tuple[UseSite, ...]]
    symbol_to_id: dict[str, int]
    id_to_symbol: tuple[str, ...]
    definitions: tuple[DefSite, ...]  # indexed by def_id

    @property
    def symbols(self) -> frozenset[str]:
        return frozenset(self.symbol_to_id)


def expr_vars(expr: ast.Expr) -> Iterator[str]:
    """Yield register names referenced by an expression (in order)."""
    if isinstance(expr, ast.Var):
        yield expr.name
    elif isinstance(expr, ast.Load):
        yield from expr_vars(expr.base)
        yield from expr_vars(expr.index)
    elif isinstance(expr, ast.Update):
        yield from expr_vars(expr.base)
        yield from expr_vars(expr.index)
        yield from expr_vars(expr.value)
    elif isinstance(expr, ast.BinExpr):
        yield from expr_vars(expr.lhs)
        yield from expr_vars(expr.rhs)
    elif isinstance(expr, ast.UnExpr):
        yield from expr_vars(expr.operand)
    elif isinstance(expr, ast.IfExpr):
        yield from expr_vars(expr.cond)
        yield from expr_vars(expr.then)
        yield from expr_vars(expr.els)
    elif isinstance(expr, ast.Record):
        yield from expr_vars(expr.addr)
        yield from expr_vars(expr.value)
        yield from expr_vars(expr.promise)
    elif isinstance(expr, ast.Field):
        yield from expr_vars(expr.base)
    # Num, BoolLit, HavocExpr contribute no variable uses.


def cmd_defs(cmd: ast.Cmd) -> tuple[ast.Target, ...]:
    """Targets a command binds (two for the mutable-borrow forms)."""
    if isinstance(cmd, (ast.Assign, ast.Havoc, ast.Phi, ast.GetRef, ast.Borrow,
                        ast.BorrowRef, ast.PutRef)):
        return (cmd.target,)
    if isinstance(cmd, ast.BorrowMut):
        return (cmd.ref_target, cmd.map_target)
    if isinstance(cmd, ast.BorrowRefMut):
        return (cmd.ref_target, cmd.cont_target)
    return ()  # Release, Assume, Assert


def cmd_uses(cmd: ast.Cmd) -> tuple[str, ...]:
    """Register names a command reads (in order, deduplicated)."""
    out: list[str] = []
    if isinstance(cmd, ast.Assign):
        out.extend(expr_vars(cmd.rhs))
    elif isinstance(cmd, ast.Phi):
        out.extend(a.value for a in cmd.arms)
    elif isinstance(cmd, ast.GetRef):
        out.append(cmd.ref)
    elif isinstance(cmd, (ast.Borrow, ast.BorrowMut)):
        out.extend(expr_vars(cmd.base))
        out.extend(expr_vars(cmd.index))
    elif isinstance(cmd, ast.BorrowRef):
        out.append(cmd.src)
    elif isinstance(cmd, ast.BorrowRefMut):
        out.append(cmd.src)
    elif isinstance(cmd, ast.PutRef):
        out.append(cmd.ref)
        out.extend(expr_vars(cmd.value))
    elif isinstance(cmd, ast.Release):
        out.append(cmd.ref)
    elif isinstance(cmd, ast.Assume):
        out.extend(expr_vars(cmd.cond))
    elif isinstance(cmd, ast.Assert):
        out.append(cmd.cond_name)
    return _dedup(out)


def terminator_uses(term: ast.Terminator) -> tuple[str, ...]:
    if isinstance(term, ast.IfGoto):
        return (term.cond,)
    return ()


def _dedup(items: list[str]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(items))


@dataclass
class _Builder:
    symbol_to_id: dict[str, int] = field(default_factory=dict)
    id_to_symbol: list[str] = field(default_factory=list)

    def sid(self, sym: str) -> int:
        if sym not in self.symbol_to_id:
            self.symbol_to_id[sym] = len(self.id_to_symbol)
            self.id_to_symbol.append(sym)
        return self.symbol_to_id[sym]


def extract_def_use(program: ast.Program) -> DefUse:
    b = _Builder()
    by_block: dict[str, BlockDefUse] = {}
    defs_by_symbol: dict[str, list[DefSite]] = defaultdict(list)
    uses_by_symbol: dict[str, list[UseSite]] = defaultdict(list)
    definitions: list[DefSite] = []

    for block in program.blocks:
        def_sites: list[DefSite] = []
        use_sites: list[UseSite] = []

        for idx, cmd in enumerate(block.commands):
            kind = type(cmd).__name__
            for sym in cmd_uses(cmd):
                us = UseSite(symbol=sym, block=block.label, cmd_index=idx, kind=kind)
                b.sid(sym)
                use_sites.append(us)
                uses_by_symbol[sym].append(us)
            for target in cmd_defs(cmd):
                sym = target.name
                ds = DefSite(
                    symbol=sym,
                    block=block.label,
                    cmd_index=idx,
                    kind=kind,
                    def_id=len(definitions),
                    symbol_id=b.sid(sym),
                )
                definitions.append(ds)
                def_sites.append(ds)
                defs_by_symbol[sym].append(ds)

        term_idx = len(block.commands)
        term_kind = type(block.terminator).__name__
        for sym in terminator_uses(block.terminator):
            us = UseSite(symbol=sym, block=block.label, cmd_index=term_idx, kind=term_kind)
            b.sid(sym)
            use_sites.append(us)
            uses_by_symbol[sym].append(us)

        by_block[block.label] = BlockDefUse(
            block=block.label,
            def_sites=tuple(def_sites),
            use_sites=tuple(use_sites),
        )

    return DefUse(
        by_block=by_block,
        defs_by_symbol={s: tuple(v) for s, v in defs_by_symbol.items()},
        uses_by_symbol={s: tuple(v) for s, v in uses_by_symbol.items()},
        symbol_to_id=dict(b.symbol_to_id),
        id_to_symbol=tuple(b.id_to_symbol),
        definitions=tuple(definitions),
    )
