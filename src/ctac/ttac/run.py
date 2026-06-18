"""Concrete interpreter for Tiny TAC (``ttac run``).

Desugar-first: references are eliminated by ``desugar_refs`` (a no-op on
reference-free programs), then the reference-free ``int``/``bool``/
``bytemap`` program is interpreted. The interpreter has no reference
logic — ``promise`` is an ordinary ``havoc`` and ``release`` an ordinary
``assume`` — so it shares one reference semantics with ``vcgen`` and a
``vcgen --model`` counterexample replays faithfully via ``--model``.

Reuses ``ctac.eval``'s ``Value`` / ``MemoryModel`` and its model parser.
"""

from __future__ import annotations

import secrets
from dataclasses import dataclass, field

from ctac.eval.model import MemoryModel, TacModel
from ctac.eval.types import Value

from . import ast
from .analysis import analyze_types
from .ast import Ty
from .pretty import cmd_str, terminator_str
from .transform import desugar_refs


class UnknownValueError(Exception):
    """A register/bytemap has no concrete value (and no model fallback)."""


def _vint(n: int) -> Value:
    return Value("int", int(n))


def _vbool(b: bool) -> Value:
    return Value("bool", bool(b))


def _as_int(v: Value) -> int:
    if v.kind == "bool":
        return 1 if v.data else 0
    return int(v.data)


def _as_bool(v: Value) -> bool:
    if v.kind == "bool":
        return bool(v.data)
    return int(v.data) != 0


def _coerce(v: Value, kind: str) -> Value:
    return _vbool(_as_bool(v)) if kind == "bool" else _vint(_as_int(v))


def _ediv(a: int, b: int) -> int:
    """SMT-LIB integer division (Euclidean): ``b==0`` -> 0."""
    if b == 0:
        return 0
    r = a % abs(b)  # Python % with a positive modulus gives r in [0, |b|)
    return (a - r) // b


@dataclass
class RunConfig:
    havoc_mode: str = "zero"  # "zero" | "random" | "ask"
    max_steps: int = 50_000
    entry: str | None = None
    model: TacModel | None = None
    validate: bool = False


@dataclass(frozen=True)
class RunEvent:
    block: str
    rendered: str
    note: str | None = None
    value: Value | None = None
    mem: str | None = None  # concrete memory access(es), e.g. "M[3]" / "M[3 := 7]"
    failed: bool = False  # this command is a failing assert (rendered red)


@dataclass
class RunResult:
    status: str  # "done" | "stopped" | "max_steps" | "error"
    reason: str
    steps: int
    executed_blocks: list[str]
    assert_ok: int
    assert_fail: int
    final_store: dict[str, Value]
    events: list[RunEvent]
    warnings: list[str] = field(default_factory=list)
    mismatches: int = 0


class _Interp:
    def __init__(self, config: RunConfig, sorts: dict[str, str | None]) -> None:
        self.config = config
        self.sorts = sorts
        self.model = config.model
        self.store: dict[str, Value] = {}
        self.memory: dict[str, MemoryModel] = {}
        self.warnings: list[str] = []
        self.assert_ok = 0
        self.assert_fail = 0
        self.mismatches = 0

    def _is_bytemap(self, name: str) -> bool:
        return self.sorts.get(name) == "bytemap"

    def _scalar_kind(self, name: str) -> str:
        return "bool" if self.sorts.get(name) == "bool" else "int"

    # --- expression evaluation ---

    def get_symbol(self, name: str) -> Value:
        if name in self.store:
            return self.store[name]
        if self.model is not None and name in self.model.values:
            return self.model.values[name]
        raise UnknownValueError(name)

    def eval(self, e: ast.Expr) -> Value:
        if isinstance(e, ast.Num):
            return _vint(e.value)
        if isinstance(e, ast.BoolLit):
            return _vbool(e.value)
        if isinstance(e, ast.Var):
            return self.get_symbol(e.name)
        if isinstance(e, ast.Load):
            mm = self._lookup_map(e.base.name if isinstance(e.base, ast.Var) else None)
            return _vint(mm.entries.get(_as_int(self.eval(e.index)), mm.default))
        if isinstance(e, ast.BinExpr):
            return self._binary(e)
        if isinstance(e, ast.UnExpr):  # not
            return _vbool(not _as_bool(self.eval(e.operand)))
        if isinstance(e, ast.IfExpr):
            return self.eval(e.then if _as_bool(self.eval(e.cond)) else e.els)
        raise ValueError(f"cannot evaluate {type(e).__name__} (desugar references first)")

    def _lookup_map(self, name: str | None) -> MemoryModel:
        if name is not None and name in self.memory:
            return self.memory[name]
        if name is not None and self.model is not None and name in self.model.memory:
            return self.model.memory[name]
        raise UnknownValueError(f"bytemap {name!r}")

    def _binary(self, e: ast.BinExpr) -> Value:
        op = e.op
        if op == "and":
            return _vbool(_as_bool(self.eval(e.lhs)) and _as_bool(self.eval(e.rhs)))
        if op == "or":
            return _vbool(_as_bool(self.eval(e.lhs)) or _as_bool(self.eval(e.rhs)))
        lhs, rhs = self.eval(e.lhs), self.eval(e.rhs)
        if op == "+":
            return _vint(_as_int(lhs) + _as_int(rhs))
        if op == "-":
            return _vint(_as_int(lhs) - _as_int(rhs))
        if op == "*":
            return _vint(_as_int(lhs) * _as_int(rhs))
        if op == "/":
            return _vint(_ediv(_as_int(lhs), _as_int(rhs)))
        if op == "<=":
            return _vbool(_as_int(lhs) <= _as_int(rhs))
        if op == "<":
            return _vbool(_as_int(lhs) < _as_int(rhs))
        if op == "==":
            if lhs.kind == "bool" or rhs.kind == "bool":
                return _vbool(_as_bool(lhs) == _as_bool(rhs))
            return _vbool(_as_int(lhs) == _as_int(rhs))
        raise ValueError(f"unsupported operator {op!r}")

    def _eval_bytemap(self, rhs: ast.Expr) -> MemoryModel:
        if isinstance(rhs, ast.Update):
            base = self._eval_bytemap(rhs.base)
            idx = _as_int(self.eval(rhs.index))
            val = _as_int(self.eval(rhs.value))
            return MemoryModel(entries={**base.entries, idx: val}, default=base.default)
        if isinstance(rhs, ast.Var):
            return self._lookup_map(rhs.name)
        raise UnknownValueError("bytemap right-hand side")

    # --- command execution: returns (note, value, stop, failed) ---

    def exec_cmd(
        self, cmd: ast.Cmd, prev: str | None
    ) -> tuple[str | None, Value | None, bool, bool]:
        if isinstance(cmd, ast.Assign):
            n, v, s = self._assign(cmd)
            return (n, v, s, False)
        if isinstance(cmd, ast.Havoc):
            n, v, s = self._havoc(cmd)
            return (n, v, s, False)
        if isinstance(cmd, ast.Phi):
            n, v, s = self._phi(cmd, prev)
            return (n, v, s, False)
        if isinstance(cmd, ast.Assume):
            try:
                ok = _as_bool(self.eval(cmd.cond))
            except UnknownValueError:
                return ("assume: unknown (skip)", None, False, False)
            if ok:
                return ("assume: true", None, False, False)
            return ("assume: false -> stop", None, True, False)
        if isinstance(cmd, ast.Assert):
            try:
                ok = _as_bool(self.get_symbol(cmd.cond_name))
            except UnknownValueError:
                return ("assert: inconclusive", None, False, False)
            if ok:
                self.assert_ok += 1
                return ("assert: ok", None, False, False)
            # A failing assert stops execution: no execution past it.
            self.assert_fail += 1
            return ("assert: FAILED", None, True, True)
        raise ValueError(f"unsupported command {type(cmd).__name__} (desugar references first)")

    def _assign(self, cmd: ast.Assign) -> tuple[str | None, Value | None, bool]:
        t = cmd.target.name
        if self._is_bytemap(t):
            try:
                self.memory[t] = self._eval_bytemap(cmd.rhs)
            except UnknownValueError:
                self.memory.pop(t, None)
                return ("bytemap: unknown", None, False)
            return ("bytemap update", None, False)
        try:
            v = self.eval(cmd.rhs)
        except UnknownValueError:
            mv = self.model.values.get(t) if self.model is not None else None
            if mv is not None:
                v = _coerce(mv, self._scalar_kind(t))
                self.store[t] = v
                return ("from model", v, False)
            self.store.pop(t, None)
            return ("unknown", None, False)
        self.store[t] = v
        return (None, v, False)

    def _havoc(self, cmd: ast.Havoc) -> tuple[str | None, Value | None, bool]:
        t = cmd.target.name
        if self._is_bytemap(t):
            if self.model is not None and t in self.model.memory:
                self.memory[t] = self.model.memory[t]
            else:
                self.memory[t] = MemoryModel(entries={}, default=0)
            return ("havoc bytemap", None, False)
        if self.model is not None and t in self.model.values:
            v = _coerce(self.model.values[t], self._scalar_kind(t))
            self.store[t] = v
            return ("havoc from model", v, False)
        v = self._havoc_value(t)
        self.store[t] = v
        return ("havoc", v, False)

    def _havoc_value(self, name: str) -> Value:
        kind = self._scalar_kind(name)
        mode = self.config.havoc_mode
        if mode == "random":
            return _vbool(secrets.randbelow(2) == 1) if kind == "bool" else _vint(secrets.randbelow(1 << 32))
        if mode == "ask":
            return self._ask(name, kind)
        return _vbool(False) if kind == "bool" else _vint(0)  # zero

    def _ask(self, name: str, kind: str) -> Value:
        try:
            raw = input(f"value for {name} ({kind})? ").strip()
        except EOFError:
            raw = ""
        if kind == "bool":
            return _vbool(raw.lower() in ("true", "1", "t", "yes"))
        try:
            return _vint(int(raw))
        except ValueError:
            return _vint(0)

    def mem_repr(self, cmd: ast.Cmd) -> str | None:
        """Concrete memory accesses in ``cmd`` with indices resolved, e.g.
        ``M[3]`` for ``x := M[i]`` or ``M[3 := 7]`` for ``M2 := M[i := v]``.
        Evaluate before the command runs so indices hold their pre-command
        values. Mirrors ctac run's counterexample memory annotation."""
        parts: list[str] = []
        if isinstance(cmd, ast.Assign):
            self._collect_mem(cmd.rhs, parts)
        elif isinstance(cmd, ast.Assume):
            self._collect_mem(cmd.cond, parts)
        return ", ".join(parts) if parts else None

    def _collect_mem(self, e: ast.Expr, parts: list[str]) -> None:
        if isinstance(e, ast.Load):
            self._collect_mem(e.base, parts)
            self._collect_mem(e.index, parts)
            base = e.base.name if isinstance(e.base, ast.Var) else "?"
            try:
                parts.append(f"{base}[{_as_int(self.eval(e.index))}]")
            except (UnknownValueError, ValueError):
                pass
        elif isinstance(e, ast.Update):
            self._collect_mem(e.base, parts)
            self._collect_mem(e.index, parts)
            self._collect_mem(e.value, parts)
            base = e.base.name if isinstance(e.base, ast.Var) else "?"
            try:
                parts.append(f"{base}[{_as_int(self.eval(e.index))} := {_as_int(self.eval(e.value))}]")
            except (UnknownValueError, ValueError):
                pass
        elif isinstance(e, ast.BinExpr):
            self._collect_mem(e.lhs, parts)
            self._collect_mem(e.rhs, parts)
        elif isinstance(e, ast.UnExpr):
            self._collect_mem(e.operand, parts)
        elif isinstance(e, ast.IfExpr):
            self._collect_mem(e.cond, parts)
            self._collect_mem(e.then, parts)
            self._collect_mem(e.els, parts)

    def _phi(self, cmd: ast.Phi, prev: str | None) -> tuple[str | None, Value | None, bool]:
        t = cmd.target.name
        arm = next((a for a in cmd.arms if a.label == prev), None)
        if arm is None:
            self.warnings.append(f"phi {t}: no arm for predecessor {prev!r}")
            self.store.pop(t, None)
            return ("phi: no matching arm", None, False)
        try:
            v = self.get_symbol(arm.value)
        except UnknownValueError:
            self.store.pop(t, None)
            return ("phi: unknown", None, False)
        self.store[t] = v
        return (None, v, False)


def run_program(program: ast.Program, *, config: RunConfig | None = None) -> RunResult:
    config = config or RunConfig()
    program = desugar_refs(program).program
    sorts = {
        name: (ty.value if isinstance(ty, Ty) else None)
        for name, ty in analyze_types(program).types.items()
    }
    interp = _Interp(config, sorts)
    by_label = {b.label: b for b in program.blocks}

    cur = config.entry or program.entry or (program.blocks[0].label if program.blocks else None)
    prev: str | None = None
    events: list[RunEvent] = []
    executed: list[str] = []
    steps = 0
    status, reason = "done", "finished"

    while cur is not None:
        if cur not in by_label:
            status, reason = "error", f"no such block {cur!r}"
            break
        if steps >= config.max_steps:
            status, reason = "max_steps", "step limit reached"
            break
        block = by_label[cur]
        executed.append(cur)
        stopped = False
        for cmd in block.commands:
            steps += 1
            mem = interp.mem_repr(cmd)  # before exec: indices hold pre-command values
            try:
                note, val, stop, failed = interp.exec_cmd(cmd, prev)
            except ValueError as exc:
                events.append(RunEvent(cur, cmd_str(cmd), f"error: {exc}", mem=mem))
                status, reason, stopped = "error", str(exc), True
                break
            events.append(RunEvent(cur, cmd_str(cmd), note, val, mem, failed))
            if failed:
                status, reason, stopped = "assert_failed", f"assertion failed in block {cur}", True
                break
            if stop:
                status, reason, stopped = "stopped", f"assume failed in block {cur}", True
                break
            if steps >= config.max_steps:
                status, reason, stopped = "max_steps", "step limit reached", True
                break
        if stopped:
            break

        term = block.terminator
        if isinstance(term, ast.Halt):
            events.append(RunEvent(cur, terminator_str(term), "halt"))
            prev, cur = cur, None
        elif isinstance(term, ast.Goto):
            events.append(RunEvent(cur, terminator_str(term), f"-> {term.target}"))
            prev, cur = cur, term.target
        elif isinstance(term, ast.IfGoto):
            try:
                take_then = _as_bool(interp.get_symbol(term.cond))
                note = f"{term.cond}={'true' if take_then else 'false'}"
            except UnknownValueError:
                interp.warnings.append(f"branch cond {term.cond!r} unknown -> then")
                take_then = True
                note = f"{term.cond}=unknown"
            target = term.then_target if take_then else term.else_target
            events.append(RunEvent(cur, terminator_str(term), f"{note} -> {target}"))
            prev, cur = cur, target

    if config.validate and interp.model is not None:
        for name, v in interp.store.items():
            mv = interp.model.values.get(name)
            if mv is not None and _coerce(mv, v.kind).data != v.data:
                interp.mismatches += 1

    return RunResult(
        status=status,
        reason=reason,
        steps=steps,
        executed_blocks=executed,
        assert_ok=interp.assert_ok,
        assert_fail=interp.assert_fail,
        final_store=dict(interp.store),
        events=events,
        warnings=interp.warnings,
        mismatches=interp.mismatches,
    )
