"""Driver for ``ttac lean``: precondition validation + text generation.

Mirrors ``vcgen/encode.py``'s shape (validate, then pure generation into
a result dataclass), but collects *all* violations before raising so a
single run reports every problem.

The v1 fragment is deliberately strict: scalars only (int/bool), pure
SSA (phi allowed, no dynamic definitions), acyclic CFG, and no
use-before-def. The last condition is load-bearing for soundness of the
deep embedding's arbitrary initial state (junk registers must be dead),
not just a lint.
"""

from __future__ import annotations

from dataclasses import dataclass

import networkx as nx

from ctac.ttac import ast
from ctac.ttac.analysis import check_dsa, infer_types
from ctac.ttac.analysis.cfg import to_digraph
from ctac.ttac.ast import Ty
from ctac.ttac.errors import LeanGenError, TtacTypeError
from ctac.ttac.pretty import cmd_str, expr_str

from . import emit
from .liveness import BlockLiveness, block_liveness
from .naming import Numbering, ShallowNames, build_numbering, build_shallow_names


@dataclass(frozen=True)
class LeanPrecheck:
    errors: tuple[str, ...]
    types: dict[str, Ty]


@dataclass(frozen=True)
class LeanResult:
    module_name: str
    deep_text: str | None  # None when the deep embedding was not requested
    shallow_text: str | None  # None when the shallow embedding was not requested
    proofs_text: str
    root_text: str
    numbering: Numbering
    liveness: BlockLiveness
    names: ShallowNames
    asserts: int


_REF_CMDS = (
    ast.GetRef,
    ast.Borrow,
    ast.BorrowMut,
    ast.BorrowRef,
    ast.BorrowRefMut,
    ast.PutRef,
    ast.Release,
)

_BYTEMAP_EXPRS = (ast.Load, ast.Update)
_REF_EXPRS = (ast.Record, ast.Field)


def _expr_children(e: ast.Expr) -> tuple[ast.Expr, ...]:
    if isinstance(e, ast.BinExpr):
        return (e.lhs, e.rhs)
    if isinstance(e, ast.UnExpr):
        return (e.operand,)
    if isinstance(e, ast.IfExpr):
        return (e.cond, e.then, e.els)
    if isinstance(e, ast.Load):
        return (e.base, e.index)
    if isinstance(e, ast.Update):
        return (e.base, e.index, e.value)
    return ()


def _bad_exprs(e: ast.Expr, *, maps: bool):
    """Yield offending non-scalar subexpressions (outermost only)."""
    if isinstance(e, _BYTEMAP_EXPRS) and not maps:
        yield e
        return
    if isinstance(e, (*_REF_EXPRS, ast.HavocExpr)):
        yield e
        return
    for child in _expr_children(e):
        yield from _bad_exprs(child, maps=maps)


def _expr_kind(e: ast.Expr) -> str:
    if isinstance(e, _BYTEMAP_EXPRS):
        return "bytemap expression"
    if isinstance(e, _REF_EXPRS):
        return "reference expression"
    return "havoc expression"


def _scalar_errors(program: ast.Program, *, maps: bool) -> list[str]:
    fragment = "int, bool, and bytemap" if maps else "only int and bool"
    errors: list[str] = []
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            where = f"block '{block.label}' cmd {idx}"
            if isinstance(cmd, _REF_CMDS):
                errors.append(
                    f"{where}: reference command '{cmd_str(cmd)}' "
                    "is not supported by ttac lean v1"
                )
                continue
            exprs: tuple[ast.Expr, ...] = ()
            targets: tuple[ast.Target, ...] = ()
            if isinstance(cmd, ast.Assign):
                exprs, targets = (cmd.rhs,), (cmd.target,)
            elif isinstance(cmd, ast.Havoc):
                targets = (cmd.target,)
            elif isinstance(cmd, ast.Phi):
                targets = (cmd.target,)
            elif isinstance(cmd, ast.Assume):
                exprs = (cmd.cond,)
            for e in exprs:
                for bad in _bad_exprs(e, maps=maps):
                    errors.append(
                        f"{where}: {_expr_kind(bad)} '{expr_str(bad)}' "
                        "is not supported here"
                    )
            bad_tys = (Ty.REF,) if maps else (Ty.BYTEMAP, Ty.REF)
            for target in targets:
                if target.ty in bad_tys:
                    errors.append(
                        f"{where}: register '{target.name}' is annotated "
                        f"'{target.ty.value}'; supported registers here are "
                        f"{fragment}"
                    )
    return errors


def _phi_errors(program: ast.Program) -> list[str]:
    errors: list[str] = []
    for block in program.blocks:
        is_entry = block.label == program.entry
        # Phis execute sequentially in the semantics (matching run.py);
        # a phi reading an earlier phi target of the same block is the
        # one shape where sequential and parallel reading differ.
        seen_targets: set[str] = set()
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, ast.Phi):
                continue
            if is_entry:
                errors.append(
                    f"block '{block.label}' cmd {idx}: phi in the entry block "
                    "has no predecessor to select an arm"
                )
            for arm in cmd.arms:
                if arm.value in seen_targets:
                    errors.append(
                        f"block '{block.label}' cmd {idx}: phi arm reads "
                        f"'{arm.value}', a phi target of the same block "
                        "(sequential phi execution would misread it)"
                    )
            seen_targets.add(cmd.target.name)
    return errors


def validate_for_lean(program: ast.Program, *, maps: bool = False) -> LeanPrecheck:
    errors: list[str] = []

    if not program.blocks or program.entry is None:
        return LeanPrecheck(errors=("empty program: nothing to embed",), types={})

    labels = {b.label for b in program.blocks}
    for block in program.blocks:
        term = block.terminator
        targets = ()
        if isinstance(term, ast.Goto):
            targets = (term.target,)
        elif isinstance(term, ast.IfGoto):
            targets = (term.then_target, term.else_target)
        for target in targets:
            if target not in labels:
                errors.append(
                    f"block '{block.label}' jumps to undefined label '{target}'"
                )

    errors.extend(_scalar_errors(program, maps=maps))
    errors.extend(_phi_errors(program))

    graph = to_digraph(program)
    acyclic = nx.is_directed_acyclic_graph(graph)
    if not acyclic:
        cycle = " -> ".join(edge[0] for edge in nx.find_cycle(graph))
        errors.append(
            f"program has a loop ({cycle} -> ...); "
            "ttac lean v1 requires a loop-free CFG"
        )

    dsa = check_dsa(program)
    for issue in dsa.issues:
        sym = f" [{issue.symbol}]" if issue.symbol else ""
        errors.append(
            f"not in SSA form: {issue.kind} at {issue.block}:{issue.cmd_index}"
            f"{sym}: {issue.detail}"
        )
    for sym in sorted(dsa.dynamic):
        errors.append(
            f"variable '{sym}' has dynamic (multi-block) definitions; "
            "ttac lean v1 requires pure SSA - rewrite the merge as a phi"
        )

    types: dict[str, Ty] = {}
    try:
        types = infer_types(program)
    except TtacTypeError as exc:
        errors.append(str(exc))
    bad_tys = (Ty.REF,) if maps else (Ty.BYTEMAP, Ty.REF)
    for name in sorted(types):
        if types[name] in bad_tys:
            fragment = "int, bool, and bytemap" if maps else "only int and bool"
            errors.append(
                f"variable '{name}' has type {types[name].value}; "
                f"supported registers here are {fragment}"
            )

    if acyclic:
        live = block_liveness(program)
        for sym in sorted(live.live_in[program.entry]):
            errors.append(
                f"variable '{sym}' may be used before it is defined "
                "(live at entry)"
            )

    return LeanPrecheck(errors=tuple(errors), types=types)


def generate_lean(
    program: ast.Program,
    *,
    module_name: str,
    source: str | None = None,
    deep: bool = True,
    shallow: bool = True,
) -> LeanResult:
    if not deep and not shallow:
        raise ValueError("at least one of deep/shallow must be requested")
    pre = validate_for_lean(program)
    if pre.errors:
        raise LeanGenError(pre.errors)

    numbering = build_numbering(program, pre.types)
    live = block_liveness(program)
    names = build_shallow_names(program, numbering)
    asserts = sum(
        isinstance(c, ast.Assert) for b in program.blocks for c in b.commands
    )
    deep_text = (
        emit.deep_module(program, numbering, pre.types, module_name, source)
        if deep
        else None
    )
    shallow_text = (
        emit.shallow_module(program, numbering, pre.types, live, names, module_name, source)
        if shallow
        else None
    )
    return LeanResult(
        module_name=module_name,
        deep_text=deep_text,
        shallow_text=shallow_text,
        proofs_text=emit.proofs_module(
            program, names, module_name, deep=deep, shallow=shallow
        ),
        root_text=emit.root_module(module_name, deep=deep, shallow=shallow),
        numbering=numbering,
        liveness=live,
        names=names,
        asserts=asserts,
    )
