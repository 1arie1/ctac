"""Borrow desugaring: a reference-free Tiny TAC source-to-source pass.

Follows the documented lowering (``doc/vc/sections/references-borrowing.typ``)
verbatim, producing the *substituted* form directly: each reference ``r``
becomes three ``int`` registers ``r__addr`` / ``r__value`` / ``r__promise``,
and every borrow command expands to ordinary assignments / a ``havoc`` /
an ``assume``. The output has no ``ref`` type, ``Record``, ``Field``, or
borrow command, so it is ready for ``vcgen``.

This is translation only: borrow well-formedness (live references,
exclusivity, reborrow lifetimes) is an external side condition the doc
leaves open. The single semantic obligation emitted is ``release``'s
``assume value == promise`` (the prophecy fulfilment).
"""

from __future__ import annotations

from dataclasses import dataclass

from ctac.ttac import ast

_FIELDS = ("addr", "value", "promise")

_BORROW_CMDS = (
    ast.Borrow,
    ast.BorrowMut,
    ast.GetRef,
    ast.PutRef,
    ast.Release,
    ast.BorrowRef,
    ast.BorrowRefMut,
)


@dataclass(frozen=True)
class DesugarResult:
    program: ast.Program
    refs_lowered: int


def _field(ref: str, fld: str) -> str:
    return f"{ref}__{fld}"


def _assign(name: str, rhs: ast.Expr) -> ast.Assign:
    return ast.Assign(ast.Target(name), rhs)


def _havoc(name: str) -> ast.Havoc:
    return ast.Havoc(ast.Target(name))


def _var(name: str) -> ast.Var:
    return ast.Var(name)


def _lower_cmd(cmd: ast.Cmd) -> list[ast.Cmd]:
    if isinstance(cmd, ast.Borrow):
        r = cmd.target.name
        return [
            _assign(_field(r, "addr"), cmd.index),
            _assign(_field(r, "value"), ast.Load(cmd.base, cmd.index)),
            _havoc(_field(r, "promise")),
        ]
    if isinstance(cmd, ast.BorrowMut):
        r = cmd.ref_target.name
        return [
            _assign(_field(r, "addr"), cmd.index),
            _assign(_field(r, "value"), ast.Load(cmd.base, cmd.index)),
            _havoc(_field(r, "promise")),
            _assign(
                cmd.map_target.name,
                ast.Update(cmd.base, cmd.index, _var(_field(r, "promise"))),
            ),
        ]
    if isinstance(cmd, ast.GetRef):
        return [_assign(cmd.target.name, _var(_field(cmd.ref, "value")))]
    if isinstance(cmd, ast.PutRef):
        t, r = cmd.target.name, cmd.ref
        return [
            _assign(_field(t, "addr"), _var(_field(r, "addr"))),
            _assign(_field(t, "value"), cmd.value),
            _assign(_field(t, "promise"), _var(_field(r, "promise"))),
        ]
    if isinstance(cmd, ast.Release):
        r = cmd.ref
        return [ast.Assume(ast.BinExpr("==", _var(_field(r, "value")), _var(_field(r, "promise"))))]
    if isinstance(cmd, ast.BorrowRef):
        q, r = cmd.target.name, cmd.src
        return [
            _assign(_field(q, "addr"), _var(_field(r, "addr"))),
            _assign(_field(q, "value"), _var(_field(r, "value"))),
            _havoc(_field(q, "promise")),
        ]
    if isinstance(cmd, ast.BorrowRefMut):
        q, r2, r = cmd.ref_target.name, cmd.cont_target.name, cmd.src
        return [
            _assign(_field(q, "addr"), _var(_field(r, "addr"))),
            _assign(_field(q, "value"), _var(_field(r, "value"))),
            _havoc(_field(q, "promise")),
            _assign(_field(r2, "addr"), _var(_field(r, "addr"))),
            _assign(_field(r2, "value"), _var(_field(q, "promise"))),
            _assign(_field(r2, "promise"), _var(_field(r, "promise"))),
        ]
    return [cmd]


def _ref_names(program: ast.Program) -> set[str]:
    """Every register that names a reference (borrow targets + ref operands).

    Excludes `BorrowMut.map_target` (a bytemap) and `GetRef.target` (an int).
    """
    names: set[str] = set()
    for block in program.blocks:
        for c in block.commands:
            if isinstance(c, ast.Borrow):
                names.add(c.target.name)
            elif isinstance(c, ast.BorrowMut):
                names.add(c.ref_target.name)
            elif isinstance(c, ast.BorrowRef):
                names.update((c.target.name, c.src))
            elif isinstance(c, ast.BorrowRefMut):
                names.update((c.ref_target.name, c.cont_target.name, c.src))
            elif isinstance(c, ast.GetRef):
                names.add(c.ref)
            elif isinstance(c, ast.PutRef):
                names.update((c.target.name, c.ref))
            elif isinstance(c, ast.Release):
                names.add(c.ref)
    return names


def _all_register_names(program: ast.Program) -> set[str]:
    names: set[str] = set()
    for block in program.blocks:
        for c in block.commands:
            for t in _targets(c):
                names.add(t)
    return names


def _targets(cmd: ast.Cmd) -> tuple[str, ...]:
    if isinstance(cmd, (ast.Assign, ast.Havoc, ast.Phi, ast.GetRef, ast.Borrow,
                        ast.BorrowRef, ast.PutRef)):
        return (cmd.target.name,)
    if isinstance(cmd, ast.BorrowMut):
        return (cmd.ref_target.name, cmd.map_target.name)
    if isinstance(cmd, ast.BorrowRefMut):
        return (cmd.ref_target.name, cmd.cont_target.name)
    return ()


def desugar_refs(program: ast.Program) -> DesugarResult:
    refs = _ref_names(program)
    generated = {_field(r, f) for r in refs for f in _FIELDS}
    clash = generated & _all_register_names(program)
    if clash:
        raise ValueError(
            f"borrow desugaring would collide with existing registers: {sorted(clash)}"
        )

    new_blocks: list[ast.Block] = []
    lowered = 0
    for block in program.blocks:
        cmds: list[ast.Cmd] = []
        for cmd in block.commands:
            if isinstance(cmd, _BORROW_CMDS):
                lowered += 1
            cmds.extend(_lower_cmd(cmd))
        new_blocks.append(ast.Block(block.label, tuple(cmds), block.terminator))

    return DesugarResult(
        program=ast.Program(tuple(new_blocks), entry=program.entry, exit=program.exit),
        refs_lowered=lowered,
    )
