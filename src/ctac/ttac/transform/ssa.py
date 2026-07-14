"""DSA -> SSA conversion for Tiny TAC.

``check_dsa`` accepts a superset of SSA: a variable may be *dynamic* -
defined once in each of several sibling predecessor blocks that share a
single merge successor. The deep/shallow Lean embeddings and other
SSA-only consumers reject that shape. :func:`to_ssa` rewrites every
dynamic variable into explicit ``phi`` form:

- each branch definition ``x := rhs`` in block ``B`` is renamed to a
  fresh per-block name ``x_B``;
- a ``phi`` binding the original name ``x`` from those fresh names is
  inserted at the top of the merge block.

Uses of ``x`` at and past the merge see the phi (name unchanged); uses
inside a branch block after its own def are switched to the fresh name.
Static and already-phi variables are untouched; a program with no
dynamic variables round-trips unchanged.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.ttac import ast

from ..analysis import cfg
from ..analysis.defuse import DefUse, extract_def_use
from ..analysis.dsa import check_dsa


@dataclass(frozen=True)
class SsaResult:
    program: ast.Program
    was_noop: bool
    converted: tuple[str, ...]  # dynamic symbols rewritten into phi form


def _rename_expr(expr: ast.Expr, m: dict[str, str]) -> ast.Expr:
    if isinstance(expr, ast.Var):
        new = m.get(expr.name)
        return ast.Var(new) if new is not None else expr
    if isinstance(expr, ast.Load):
        return ast.Load(_rename_expr(expr.base, m), _rename_expr(expr.index, m))
    if isinstance(expr, ast.Update):
        return ast.Update(
            _rename_expr(expr.base, m),
            _rename_expr(expr.index, m),
            _rename_expr(expr.value, m),
        )
    if isinstance(expr, ast.BinExpr):
        return ast.BinExpr(expr.op, _rename_expr(expr.lhs, m), _rename_expr(expr.rhs, m))
    if isinstance(expr, ast.UnExpr):
        return ast.UnExpr(expr.op, _rename_expr(expr.operand, m))
    if isinstance(expr, ast.IfExpr):
        return ast.IfExpr(
            _rename_expr(expr.cond, m),
            _rename_expr(expr.then, m),
            _rename_expr(expr.els, m),
        )
    if isinstance(expr, ast.Record):
        return ast.Record(
            _rename_expr(expr.addr, m),
            _rename_expr(expr.value, m),
            _rename_expr(expr.promise, m),
        )
    if isinstance(expr, ast.Field):
        return ast.Field(_rename_expr(expr.base, m), expr.name)
    return expr


def _rename_name(name: str, m: dict[str, str]) -> str:
    return m.get(name, name)


def _rename_cmd_uses(cmd: ast.Cmd, m: dict[str, str]) -> ast.Cmd:
    """Rename only the *use* positions of ``cmd``; targets are untouched."""
    if isinstance(cmd, ast.Assign):
        return replace(cmd, rhs=_rename_expr(cmd.rhs, m))
    if isinstance(cmd, ast.Phi):
        arms = tuple(
            ast.PhiArm(a.label, _rename_name(a.value, m)) for a in cmd.arms
        )
        return replace(cmd, arms=arms)
    if isinstance(cmd, ast.GetRef):
        return replace(cmd, ref=_rename_name(cmd.ref, m))
    if isinstance(cmd, ast.Borrow):
        return replace(cmd, base=_rename_expr(cmd.base, m), index=_rename_expr(cmd.index, m))
    if isinstance(cmd, ast.BorrowMut):
        return replace(cmd, base=_rename_expr(cmd.base, m), index=_rename_expr(cmd.index, m))
    if isinstance(cmd, ast.BorrowRef):
        return replace(cmd, src=_rename_name(cmd.src, m))
    if isinstance(cmd, ast.BorrowRefMut):
        return replace(cmd, src=_rename_name(cmd.src, m))
    if isinstance(cmd, ast.PutRef):
        return replace(cmd, ref=_rename_name(cmd.ref, m), value=_rename_expr(cmd.value, m))
    if isinstance(cmd, ast.Release):
        return replace(cmd, ref=_rename_name(cmd.ref, m))
    if isinstance(cmd, ast.Assume):
        return replace(cmd, cond=_rename_expr(cmd.cond, m))
    if isinstance(cmd, ast.Assert):
        return replace(cmd, cond_name=_rename_name(cmd.cond_name, m))
    return cmd


def _rename_term_uses(term: ast.Terminator, m: dict[str, str]) -> ast.Terminator:
    if isinstance(term, ast.IfGoto):
        return replace(term, cond=_rename_name(term.cond, m))
    return term


def _retarget(cmd: ast.Cmd, old: str, new: str) -> ast.Cmd:
    """Rename the single scalar def target ``old`` -> ``new`` of ``cmd``."""
    tgt = getattr(cmd, "target", None)
    if isinstance(tgt, ast.Target) and tgt.name == old:
        return replace(cmd, target=replace(tgt, name=new))
    return cmd


def _fresh(base: str, block: str, taken: set[str]) -> str:
    cand = f"{base}_{block}"
    n = 1
    while cand in taken:
        cand = f"{base}_{block}_{n}"
        n += 1
    taken.add(cand)
    return cand


def to_ssa(program: ast.Program, *, def_use: DefUse | None = None) -> SsaResult:
    du = def_use if def_use is not None else extract_def_use(program)
    dsa = check_dsa(program, def_use=du)
    if not dsa.dynamic:
        return SsaResult(program=program, was_noop=True, converted=())

    preds = cfg.predecessors(program)
    succ = {
        b.label: tuple(cfg.successors(b)) for b in program.blocks
    }

    taken = set(du.symbols)
    # Per (block, symbol) fresh name for each dynamic def; per merge block
    # the phi arms to insert.
    fresh: dict[tuple[str, str], str] = {}
    merge_phis: dict[str, list[ast.Phi]] = {}
    for sym in sorted(dsa.dynamic):
        defs = du.defs_by_symbol[sym]
        merge = succ[defs[0].block][0]
        arms: list[ast.PhiArm] = []
        for d in defs:
            f = _fresh(sym, d.block, taken)
            fresh[(d.block, sym)] = f
            arms.append(ast.PhiArm(d.block, f))
        arm_order = {a.label: a for a in arms}
        ordered = tuple(arm_order[p] for p in preds[merge] if p in arm_order)
        merge_phis.setdefault(merge, []).append(
            ast.Phi(target=ast.Target(sym), arms=ordered)
        )

    def_index: dict[tuple[str, str], int] = {}
    for (blk, sym) in fresh:
        for d in du.defs_by_symbol[sym]:
            if d.block == blk:
                def_index[(blk, sym)] = d.cmd_index

    new_blocks: list[ast.Block] = []
    for block in program.blocks:
        local = {
            sym: fresh[(block.label, sym)]
            for (blk, sym) in fresh
            if blk == block.label
        }
        active: dict[str, str] = {}
        out_cmds: list[ast.Cmd] = []
        for idx, cmd in enumerate(block.commands):
            cmd = _rename_cmd_uses(cmd, active)
            for sym, f in local.items():
                if def_index.get((block.label, sym)) == idx:
                    cmd = _retarget(cmd, sym, f)
                    active[sym] = f
            out_cmds.append(cmd)
        term = _rename_term_uses(block.terminator, active)
        phis = merge_phis.get(block.label, [])
        new_blocks.append(
            replace(block, commands=tuple(phis) + tuple(out_cmds), terminator=term)
        )

    return SsaResult(
        program=replace(program, blocks=tuple(new_blocks)),
        was_noop=False,
        converted=tuple(sorted(dsa.dynamic)),
    )
