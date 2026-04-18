"""TAC program interpreter with pluggable havoc modes and optional trace."""

from __future__ import annotations

import json
import re
import secrets
from dataclasses import dataclass, field
from typing import Callable, Literal

from ctac.ir.models import TacBlock, TacProgram
from ctac.eval.constants import MOD_256, SIGN_BIT_256
from ctac.eval.types import HavocMode, Value, ValueKind
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    SymExpr,
    TacCmd,
    TacExpr,
)

_META_SUFFIX_RE = re.compile(r":\d+$")


@dataclass
class RunConfig:
    entry_block: str | None = None
    max_steps: int = 50_000
    havoc_mode: HavocMode = "zero"
    initial_store: dict[str, Value] = field(default_factory=dict)
    ask_value: Callable[[str, ValueKind], Value] | None = None
    strip_var_suffixes: bool = True


@dataclass
class RunEvent:
    block_id: str
    cmd: TacCmd
    rendered: str
    note: str | None = None
    color: str | None = None
    value: Value | None = None
    expected: Value | None = None
    mismatch: bool = False


@dataclass
class RunResult:
    status: Literal["stopped", "max_steps", "done", "error"]
    reason: str
    steps: int
    final_store: dict[str, Value]
    executed_blocks: list[str]
    assert_ok: int
    assert_fail: int
    events: list[RunEvent]


def infer_kind(symbol: str) -> ValueKind:
    s = symbol.strip()
    if s.startswith("B"):
        return "bool"
    if s.startswith("I"):
        return "int"
    return "bv"


def canonical_symbol(symbol: str, *, strip_var_suffixes: bool) -> str:
    s = symbol.strip()
    if strip_var_suffixes:
        return _META_SUFFIX_RE.sub("", s)
    return s


def value_to_text(v: Value) -> str:
    if v.kind == "bool":
        return "true" if bool(v.data) else "false"
    if v.kind == "bv":
        return hex(int(v.data) % MOD_256)
    return str(int(v.data))


def _typed_const_kind(tag: str) -> ValueKind:
    t = tag.lower()
    if t == "int":
        return "int"
    if t == "bool":
        return "bool"
    return "bv"


def _parse_const(s: str) -> Value:
    t = s.strip()
    if t == "true":
        return Value("bool", True)
    if t == "false":
        return Value("bool", False)
    # typed numeric constant, e.g. 0x100(int)
    if t.endswith(")") and "(" in t:
        lp = t.rfind("(")
        rp = t.rfind(")")
        if rp == len(t) - 1 and lp > 0:
            base = t[:lp]
            tag = t[lp + 1 : rp]
            if base.startswith(("0x", "0X")):
                n = int(base, 16)
            else:
                n = int(base, 10)
            k = _typed_const_kind(tag)
            if k == "bv":
                return Value("bv", n % MOD_256)
            if k == "bool":
                return Value("bool", bool(n))
            return Value("int", n)
    if t.startswith(("0x", "0X")):
        return Value("bv", int(t, 16) % MOD_256)
    return Value("int", int(t, 10))


def _as_bool(v: Value) -> bool:
    if v.kind == "bool":
        return bool(v.data)
    return int(v.data) != 0


def _as_int(v: Value) -> int:
    if v.kind == "bool":
        return 1 if bool(v.data) else 0
    return int(v.data)


def _as_bv(v: Value) -> int:
    return _as_int(v) % MOD_256


def _signed_256(x: int) -> int:
    x = x % MOD_256
    return x - MOD_256 if x >= SIGN_BIT_256 else x


def _mk_bv(x: int) -> Value:
    return Value("bv", x % MOD_256)


def _mk_int(x: int) -> Value:
    return Value("int", int(x))


def _mk_bool(x: bool) -> Value:
    return Value("bool", bool(x))


def _parse_snippet_cmd(payload: str) -> dict[str, object] | None:
    s = payload.strip()
    if not s.startswith("JSON"):
        return None
    try:
        obj = json.loads(s[4:])
    except json.JSONDecodeError:
        return None
    if not isinstance(obj, dict):
        return None
    key = obj.get("key")
    val = obj.get("value")
    if not isinstance(key, dict) or not isinstance(val, dict):
        return None
    if key.get("name") != "snippet.cmd":
        return None
    klass = val.get("#class")
    if not isinstance(klass, str):
        return None

    if klass.endswith(".ScopeStart"):
        scope = val.get("scopeName")
        if isinstance(scope, str):
            return {"kind": "scope_start", "scope": scope}
        return None
    if klass.endswith(".ScopeEnd"):
        scope = val.get("scopeName")
        if isinstance(scope, str):
            return {"kind": "scope_end", "scope": scope}
        return None
    if klass.endswith(".CexPrintValues"):
        msg = val.get("displayMessage")
        syms = val.get("symbols")
        if not isinstance(msg, str) or not isinstance(syms, list) or not syms:
            return None
        first = syms[0]
        if not isinstance(first, dict):
            return None
        reg = first.get("namePrefix")
        if not isinstance(reg, str):
            return None
        return {"kind": "print_value", "tag": msg, "symbol": reg}
    if klass.endswith(".CexPrint128BitsValue"):
        msg = val.get("displayMessage")
        low = val.get("low")
        high = val.get("high")
        signed = bool(val.get("signed", False))
        if not isinstance(msg, str) or not isinstance(low, dict) or not isinstance(high, dict):
            return None
        low_sym = low.get("namePrefix")
        high_sym = high.get("namePrefix")
        if not isinstance(low_sym, str) or not isinstance(high_sym, str):
            return None
        return {
            "kind": "print_128",
            "tag": msg,
            "low": low_sym,
            "high": high_sym,
            "signed": signed,
        }
    if klass.endswith(".CexPrintTag"):
        msg = val.get("displayMessage")
        if not isinstance(msg, str):
            return None
        return {"kind": "print_tag", "tag": msg}
    return None


def _compose_128_from_regs(low: Value, high: Value, *, signed: bool) -> Value:
    mask64 = (1 << 64) - 1
    lo = _as_bv(low) & mask64
    hi = _as_bv(high) & mask64
    u = (hi << 64) | lo
    if signed and (u & (1 << 127)):
        return _mk_int(u - (1 << 128))
    return _mk_int(u)


def _havoc_value(symbol: str, mode: HavocMode, ask_value: Callable[[str, ValueKind], Value] | None) -> Value:
    k = infer_kind(symbol)
    if mode == "zero":
        return _mk_bool(False) if k == "bool" else (_mk_int(0) if k == "int" else _mk_bv(0))
    if mode == "ask":
        if ask_value is None:
            raise ValueError("havoc mode 'ask' requires ask_value callback")
        return ask_value(symbol, k)
    # random
    if k == "bool":
        return _mk_bool(bool(secrets.randbelow(2)))
    if k == "int":
        return _mk_int(secrets.randbelow(1 << 64))
    return _mk_bv(secrets.randbelow(MOD_256))


class Evaluator:
    def __init__(self, store: dict[str, Value], *, normalize_symbol: Callable[[str], str]):
        self.store = store
        self._normalize_symbol = normalize_symbol

    def get_symbol(self, name: str) -> Value:
        key = self._normalize_symbol(name)
        if key not in self.store:
            k = infer_kind(key)
            self.store[key] = _mk_bool(False) if k == "bool" else (_mk_int(0) if k == "int" else _mk_bv(0))
        return self.store[key]

    def eval_expr(self, expr: TacExpr) -> Value:
        if isinstance(expr, ConstExpr):
            return _parse_const(expr.value)
        if isinstance(expr, SymExpr):
            return self.get_symbol(expr.name)
        if isinstance(expr, ApplyExpr):
            return self._eval_apply(expr.op, [self.eval_expr(a) for a in expr.args], expr)
        raise TypeError(f"unsupported expr node: {type(expr).__name__}")

    def _eval_apply(self, op: str, args: list[Value], whole: ApplyExpr) -> Value:
        if op == "Ite" and len(args) == 3:
            return args[1] if _as_bool(args[0]) else args[2]

        if op == "Apply" and len(args) >= 2 and isinstance(whole.args[0], SymExpr):
            fn = whole.args[0].name
            if fn.startswith("safe_math_narrow_bv256"):
                return _mk_bv(_as_int(args[1]))
            # unknown builtin/application: conservative fallback
            return args[1]

        if op in {"LAnd", "LOr"} and args:
            if op == "LAnd":
                return _mk_bool(all(_as_bool(a) for a in args))
            return _mk_bool(any(_as_bool(a) for a in args))
        if op == "LNot" and len(args) == 1:
            return _mk_bool(not _as_bool(args[0]))

        if op in {"Eq", "Lt", "Le", "Gt", "Ge", "Slt", "Sle", "Sgt", "Sge"} and len(args) == 2:
            a, b = args
            if op == "Eq":
                return _mk_bool(_as_int(a) == _as_int(b))
            if op == "Lt":
                return _mk_bool(_as_bv(a) < _as_bv(b))
            if op == "Le":
                return _mk_bool(_as_bv(a) <= _as_bv(b))
            if op == "Gt":
                return _mk_bool(_as_bv(a) > _as_bv(b))
            if op == "Ge":
                return _mk_bool(_as_bv(a) >= _as_bv(b))
            if op == "Slt":
                return _mk_bool(_signed_256(_as_bv(a)) < _signed_256(_as_bv(b)))
            if op == "Sle":
                return _mk_bool(_signed_256(_as_bv(a)) <= _signed_256(_as_bv(b)))
            if op == "Sgt":
                return _mk_bool(_signed_256(_as_bv(a)) > _signed_256(_as_bv(b)))
            return _mk_bool(_signed_256(_as_bv(a)) >= _signed_256(_as_bv(b)))

        if op in {"BWAnd", "BWOr", "BWXOr"} and len(args) >= 2:
            xs = [_as_bv(a) for a in args]
            acc = xs[0]
            for x in xs[1:]:
                if op == "BWAnd":
                    acc &= x
                elif op == "BWOr":
                    acc |= x
                else:
                    acc ^= x
            return _mk_bv(acc)
        if op == "BWNot" and len(args) == 1:
            return _mk_bv(~_as_bv(args[0]))

        if op in {"ShiftLeft", "ShiftRightLogical", "ShiftRightArithmetical"} and len(args) == 2:
            a, b = _as_bv(args[0]), _as_int(args[1])
            sh = max(0, min(4096, b))
            if op == "ShiftLeft":
                return _mk_bv(a << sh)
            if op == "ShiftRightLogical":
                return _mk_bv(a >> sh)
            return _mk_bv(_signed_256(a) >> sh)

        if op in {"Add", "Sub", "Mul", "Div", "Mod"} and len(args) >= 2:
            xs = [_as_bv(a) for a in args]
            acc = xs[0]
            for x in xs[1:]:
                if op == "Add":
                    acc = (acc + x) % MOD_256
                elif op == "Sub":
                    acc = (acc - x) % MOD_256
                elif op == "Mul":
                    acc = (acc * x) % MOD_256
                elif op == "Div":
                    acc = 0 if x == 0 else (acc // x)
                else:
                    acc = 0 if x == 0 else (acc % x)
            return _mk_bv(acc)

        if op in {"IntAdd", "IntSub", "IntMul", "IntDiv", "IntMod"} and len(args) >= 2:
            xs = [_as_int(a) for a in args]
            acc = xs[0]
            for x in xs[1:]:
                if op == "IntAdd":
                    acc = acc + x
                elif op == "IntSub":
                    acc = acc - x
                elif op == "IntMul":
                    acc = acc * x
                elif op == "IntDiv":
                    acc = 0 if x == 0 else (acc // x)
                else:
                    acc = 0 if x == 0 else (acc % x)
            return _mk_int(acc)

        # Unknown op fallback: return first argument if present, otherwise 0 bv.
        return args[0] if args else _mk_bv(0)


def _default_entry(program: TacProgram) -> str | None:
    if not program.blocks:
        return None
    return program.blocks[0].id


def run_program(
    program: TacProgram,
    *,
    config: RunConfig | None = None,
    pretty_cmd: Callable[[TacCmd], str | None] | None = None,
) -> RunResult:
    cfg = config or RunConfig()
    normalize_symbol = lambda s: canonical_symbol(s, strip_var_suffixes=cfg.strip_var_suffixes)
    store = {normalize_symbol(k): v for k, v in cfg.initial_store.items()}
    ev = Evaluator(store, normalize_symbol=normalize_symbol)
    blocks_by_id = program.block_by_id()
    entry = cfg.entry_block or _default_entry(program)
    if entry is None:
        return RunResult(
            status="done",
            reason="empty program",
            steps=0,
            final_store=store,
            executed_blocks=[],
            assert_ok=0,
            assert_fail=0,
            events=[],
        )
    if entry not in blocks_by_id:
        return RunResult(
            status="error",
            reason=f"entry block {entry!r} not found",
            steps=0,
            final_store=store,
            executed_blocks=[],
            assert_ok=0,
            assert_fail=0,
            events=[],
        )

    status: Literal["stopped", "max_steps", "done", "error"] = "done"
    reason = "finished"
    steps = 0
    assert_ok = 0
    assert_fail = 0
    events: list[RunEvent] = []
    executed_blocks: list[str] = []
    seen = set()

    current = entry
    while current is not None:
        if steps >= cfg.max_steps:
            status = "max_steps"
            reason = f"max steps reached ({cfg.max_steps})"
            break
        if current not in blocks_by_id:
            status = "error"
            reason = f"jumped to missing block {current!r}"
            break
        block: TacBlock = blocks_by_id[current]
        if current not in seen:
            seen.add(current)
            executed_blocks.append(current)

        next_block: str | None = None
        stop_now = False

        for cmd in block.commands:
            if steps >= cfg.max_steps:
                status = "max_steps"
                reason = f"max steps reached ({cfg.max_steps})"
                stop_now = True
                break
            steps += 1

            rendered = pretty_cmd(cmd) if pretty_cmd is not None else cmd.raw
            if rendered is None:
                rendered = ""

            if isinstance(cmd, AssignExpCmd):
                val = ev.eval_expr(cmd.rhs)
                ev.store[normalize_symbol(cmd.lhs)] = val
                events.append(RunEvent(current, cmd, rendered, value=val))
                continue

            if isinstance(cmd, AssignHavocCmd):
                v = _havoc_value(cmd.lhs, cfg.havoc_mode, cfg.ask_value)
                ev.store[normalize_symbol(cmd.lhs)] = v
                events.append(RunEvent(current, cmd, rendered, value=v))
                continue

            if isinstance(cmd, AssumeExpCmd):
                cond = ev.eval_expr(cmd.condition)
                ok = _as_bool(cond)
                if ok:
                    events.append(RunEvent(current, cmd, rendered, note="true", color="green"))
                else:
                    events.append(RunEvent(current, cmd, rendered, note="false -> stop", color="red"))
                    status = "stopped"
                    reason = f"assume failed in block {current}"
                    stop_now = True
                    break
                continue

            if isinstance(cmd, AssertCmd):
                pred = ev.get_symbol(cmd.predicate)
                ok = _as_bool(pred)
                if ok:
                    assert_ok += 1
                    events.append(RunEvent(current, cmd, rendered, note="ok", color="green"))
                else:
                    assert_fail += 1
                    events.append(RunEvent(current, cmd, rendered, note="FAILED (continue)", color="red"))
                continue

            if isinstance(cmd, JumpiCmd):
                cv = ev.get_symbol(cmd.condition)
                take_then = _as_bool(cv)
                next_block = cmd.then_target if take_then else cmd.else_target
                note = next_block
                cond_txt = canonical_symbol(cmd.condition, strip_var_suffixes=cfg.strip_var_suffixes)
                shown = rendered or f"if {cond_txt} goto {cmd.then_target} else {cmd.else_target}"
                events.append(RunEvent(current, cmd, shown, note=note, color="green"))
                break

            if isinstance(cmd, JumpCmd):
                next_block = cmd.target
                shown = rendered or f"goto {cmd.target}"
                events.append(RunEvent(current, cmd, shown, note=next_block, color="green"))
                break

            if isinstance(cmd, AnnotationCmd):
                snippet = _parse_snippet_cmd(cmd.payload)
                if snippet is not None:
                    kind = snippet["kind"]
                    if kind == "scope_start":
                        scope = str(snippet["scope"])
                        events.append(RunEvent(current, cmd, scope, color="bold cyan"))
                        continue
                    if kind == "scope_end":
                        # ScopeEnd is structural; no dedicated output line needed.
                        continue
                    if kind == "print_value":
                        tag = str(snippet["tag"])
                        sym = str(snippet["symbol"])
                        v = ev.get_symbol(sym)
                        events.append(RunEvent(current, cmd, f"  {tag}", value=v, color="cyan"))
                        continue
                    if kind == "print_128":
                        tag = str(snippet["tag"])
                        low = ev.get_symbol(str(snippet["low"]))
                        high = ev.get_symbol(str(snippet["high"]))
                        v = _compose_128_from_regs(low, high, signed=bool(snippet["signed"]))
                        events.append(RunEvent(current, cmd, f"  {tag}", value=v, color="cyan"))
                        continue
                    if kind == "print_tag":
                        tag = str(snippet["tag"])
                        events.append(RunEvent(current, cmd, f"  {tag}", color="cyan"))
                        continue
                if rendered:
                    events.append(RunEvent(current, cmd, rendered))
                continue

            if isinstance(cmd, (LabelCmd, RawCmd)):
                if rendered:
                    events.append(RunEvent(current, cmd, rendered))
                continue

        if stop_now:
            break

        if next_block is None:
            if block.successors:
                if len(block.successors) == 1:
                    next_block = block.successors[0]
                else:
                    next_block = block.successors[0]
                    events.append(
                        RunEvent(
                            current,
                            RawCmd(raw="implicit_fallthrough", head="implicit", tail=""),
                            "implicit fallthrough",
                            note=f"take {next_block}; other successors ignored",
                            color="cyan",
                        )
                    )
            else:
                status = "done"
                reason = f"terminated at block {current}"
                break

        current = next_block

    return RunResult(
        status=status,
        reason=reason,
        steps=steps,
        final_store=ev.store,
        executed_blocks=executed_blocks,
        assert_ok=assert_ok,
        assert_fail=assert_fail,
        events=events,
    )
