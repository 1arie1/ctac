"""TAC program interpreter with pluggable havoc modes and optional trace."""

from __future__ import annotations

import json
import re
import secrets
from dataclasses import dataclass, field
from typing import Callable, Literal

from ctac.ir.models import TacBlock, TacProgram
from ctac.builtins import is_known_builtin_function_symbol
from ctac.eval.constants import MOD_256, SIGN_BIT_256
from ctac.eval.model import MemoryModel
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
    SymbolRef,
    SymExpr,
    SymbolWeakRef,
    TacCmd,
    TacExpr,
)

_META_SUFFIX_RE = re.compile(r":\d+$")


class UnknownValueError(Exception):
    """Signals that an expression cannot be evaluated concretely.

    Raised when the interpreter hits a `Select` on an unknown bytemap or
    an `_eval_bytemap_expr` chain rooted at a name with no entry in
    `memory_store`. Propagates through arithmetic / boolean operators
    untouched (operands raise before the op runs); the command loop
    catches it at `AssignExpCmd` and falls back to `model_values[lhs]`.
    """


@dataclass
class RunConfig:
    entry_block: str | None = None
    max_steps: int = 50_000
    havoc_mode: HavocMode = "zero"
    initial_store: dict[str, Value] = field(default_factory=dict)
    ask_value: Callable[[str, ValueKind], Value] | None = None
    strip_var_suffixes: bool = True
    # Per-bytemap read map, keyed by canonical symbol name. Each entry
    # has ``.entries`` (index -> value) and ``.default``. ``Select(M,
    # idx)`` looks up ``entries[idx]``, falling back to ``default``.
    memory_store: dict[str, "object"] = field(default_factory=dict)
    # Sort table from the parser; used to detect bytemap/ghostmap LHS.
    symbol_sorts: dict[str, str] = field(default_factory=dict)
    # Model values consulted at AssignExpCmd when concrete eval fails.
    model_values: dict[str, Value] = field(default_factory=dict)


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
    # Provenance of `value` when it came from a model-driven havoc.
    # Set post-hoc by the CLI (commands_run) for AssignHavocCmd events:
    # ``"model"`` (primary --model hit), ``"fallback"`` (--fallback hit),
    # ``"default"`` (unconstrained sentinel = MODEL_HAVOC_FALLBACK_NUM).
    # ``None`` for everything else (computed values, no --model run, etc.).
    value_source: str | None = None
    # Concretized memory-op annotation for display in the trace's value
    # pane. Only set when an AssignExpCmd's RHS is a bytemap Store or
    # contains a Select with a *symbolic* key/val operand — otherwise the
    # cmd line itself already shows the literal indices and there's no
    # extra information to surface. Stores look like
    # ``M0[<key_hex> := <val_hex>]``; loads like ``M[<key_hex>]`` (one
    # entry per Select, comma-joined when multiple).
    memory_repr: str | None = None


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


def _parse_signed_hex_or_dec(base: str) -> int:
    """Parse ``0x...``, ``0x-...``, ``-0x...``, or a decimal literal.

    The Certora TAC printer emits negative hex constants as ``0x-N`` (sign
    *after* the radix prefix). ``int(..., 16)`` doesn't accept that shape,
    so normalize to the standard ``-0x...`` form first.
    """
    s = base.strip()
    sl = s.lower()
    if sl.startswith("0x-") or sl.startswith("0x+"):
        return int(s[0:2] + s[3:], 16) * (-1 if s[2] == "-" else 1)
    if sl.startswith(("0x", "-0x", "+0x")):
        return int(s, 16)
    return int(s, 10)


def _parse_const(s: str) -> Value:
    t = s.strip()
    if t == "true":
        return Value("bool", True)
    if t == "false":
        return Value("bool", False)
    # typed numeric constant, e.g. 0x100(int) or 0x-48(int)
    if t.endswith(")") and "(" in t:
        lp = t.rfind("(")
        rp = t.rfind(")")
        if rp == len(t) - 1 and lp > 0:
            base = t[:lp]
            tag = t[lp + 1 : rp]
            n = _parse_signed_hex_or_dec(base)
            k = _typed_const_kind(tag)
            if k == "bv":
                return Value("bv", n % MOD_256)
            if k == "bool":
                return Value("bool", bool(n))
            return Value("int", n)
    if t.startswith(("0x", "0X", "-0x", "-0X")):
        return Value("bv", _parse_signed_hex_or_dec(t) % MOD_256)
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


def _parse_snippet_cmd(payload: str, *, weak_is_strong: bool = False) -> dict[str, object] | None:
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
        ref = SymbolRef(reg) if weak_is_strong else SymbolWeakRef(reg)
        return {"kind": "print_value", "tag": msg, "symbol": ref}
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
        low_ref = SymbolRef(low_sym) if weak_is_strong else SymbolWeakRef(low_sym)
        high_ref = SymbolRef(high_sym) if weak_is_strong else SymbolWeakRef(high_sym)
        return {
            "kind": "print_128",
            "tag": msg,
            "low": low_ref,
            "high": high_ref,
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


def _format_bytemap_store_repr(ev: "Evaluator", rhs: TacExpr) -> str | None:
    """If ``rhs`` (descending through Ite wrappers along the chosen branch)
    bottoms out at ``Store(M0, key, val)`` and at least one of key/val is
    not a literal constant, return ``"M0[<key_hex> := <val_hex>]"`` using
    the live evaluator's view of those operands. Returns ``None`` when the
    shape doesn't match or when the model can't concretize the operands —
    callers should treat this as "no extra info to surface".
    """
    expr = rhs
    while isinstance(expr, ApplyExpr) and expr.op == "Ite" and len(expr.args) == 3:
        try:
            cond = ev.eval_expr(expr.args[0])
        except UnknownValueError:
            return None
        expr = expr.args[1] if _as_bool(cond) else expr.args[2]
    if not (isinstance(expr, ApplyExpr) and expr.op == "Store" and len(expr.args) == 3):
        return None
    m_arg, k_arg, v_arg = expr.args
    if isinstance(k_arg, ConstExpr) and isinstance(v_arg, ConstExpr):
        return None
    try:
        k_val = ev.eval_expr(k_arg)
        v_val = ev.eval_expr(v_arg)
    except UnknownValueError:
        return None
    m_name = m_arg.name if isinstance(m_arg, SymExpr) else "?"
    return f"{m_name}[{value_to_text(k_val)} := {value_to_text(v_val)}]"


def _format_bytemap_select_reprs(ev: "Evaluator", rhs: TacExpr) -> str | None:
    """Walk ``rhs``; for every ``Select(M, k)`` whose key is not a literal
    constant, format ``"M[<key_hex>]"`` using the live evaluator.
    Multiple Selects in the same RHS (rare but possible) are joined with
    ``", "``. Returns ``None`` if no symbolic Select is reached.
    """
    parts: list[str] = []
    seen: set[tuple[str, str]] = set()

    def _walk(e: TacExpr) -> None:
        if not isinstance(e, ApplyExpr):
            return
        if e.op == "Select" and len(e.args) == 2:
            m_arg, k_arg = e.args
            if not isinstance(k_arg, ConstExpr):
                try:
                    k_val = ev.eval_expr(k_arg)
                except UnknownValueError:
                    return
                m_name = m_arg.name if isinstance(m_arg, SymExpr) else "?"
                key = (m_name, value_to_text(k_val))
                if key not in seen:
                    seen.add(key)
                    parts.append(f"{m_name}[{key[1]}]")
                return  # don't dig past the Select boundary
        for a in e.args:
            _walk(a)

    _walk(rhs)
    return ", ".join(parts) if parts else None


class Evaluator:
    def __init__(
        self,
        store: dict[str, Value],
        *,
        normalize_symbol: Callable[[str], str],
        memory_store: dict[str, object] | None = None,
        symbol_sorts: dict[str, str] | None = None,
        model_values: dict[str, Value] | None = None,
    ):
        self.store = store
        self._normalize_symbol = normalize_symbol
        self.memory_store = memory_store if memory_store is not None else {}
        self._symbol_sorts = symbol_sorts if symbol_sorts is not None else {}
        self.model_values = model_values if model_values is not None else {}

    def get_symbol(self, name: str) -> Value:
        key = self._normalize_symbol(name)
        if key in self.store:
            return self.store[key]
        v = self.model_values.get(key)
        if v is not None:
            return v
        raise UnknownValueError(f"no value for {key!r}")

    def peek_symbol(self, name: str) -> Value | None:
        key = self._normalize_symbol(name)
        return self.store.get(key)

    def _is_bytemap_name(self, name: str) -> bool:
        sort = self._symbol_sorts.get(self._normalize_symbol(name))
        return sort in ("bytemap", "ghostmap")

    def _eval_select(self, expr: ApplyExpr) -> Value:
        if len(expr.args) != 2 or not isinstance(expr.args[0], SymExpr):
            raise ValueError("Select expects (memory_symbol, index)")
        mem_name = self._normalize_symbol(expr.args[0].name)
        idx = _as_int(self.eval_expr(expr.args[1]))
        mem = self.memory_store.get(mem_name)
        if mem is None:
            raise UnknownValueError(f"select on unknown bytemap {mem_name!r}")
        default = getattr(mem, "default", 0)
        entries = getattr(mem, "entries", None) or {}
        val = entries.get(idx, default)
        return _mk_bv(val % MOD_256)

    def _eval_bytemap_expr(self, expr: TacExpr) -> MemoryModel:
        if isinstance(expr, SymExpr):
            name = self._normalize_symbol(expr.name)
            mm = self.memory_store.get(name)
            if mm is None:
                raise UnknownValueError(f"unknown bytemap {name!r}")
            # ``MemoryModel`` is frozen; sharing the instance is safe.
            return mm  # type: ignore[return-value]
        if isinstance(expr, ApplyExpr):
            if expr.op == "Store" and len(expr.args) == 3:
                old = self._eval_bytemap_expr(expr.args[0])
                k = _as_int(self.eval_expr(expr.args[1]))
                v = _as_int(self.eval_expr(expr.args[2]))
                return MemoryModel(
                    entries={**old.entries, k: v}, default=old.default
                )
            if expr.op == "Ite" and len(expr.args) == 3:
                cond = self.eval_expr(expr.args[0])
                chosen = expr.args[1] if _as_bool(cond) else expr.args[2]
                return self._eval_bytemap_expr(chosen)
        raise ValueError(
            f"unsupported bytemap expression: {type(expr).__name__}"
            f" {getattr(expr, 'op', '')}"
        )

    def eval_expr(self, expr: TacExpr) -> Value:
        if isinstance(expr, ConstExpr):
            return _parse_const(expr.value)
        if isinstance(expr, SymExpr):
            return self.get_symbol(expr.name)
        if isinstance(expr, ApplyExpr):
            # Select memory reads don't go through the generic _eval_apply
            # fallback — the memory arg is a SymbolRef, not a Value.
            if expr.op == "Select":
                return self._eval_select(expr)
            # Ite is dispatched lazily so the unchosen branch is not
            # forced — necessary when one branch is genuinely unknown
            # (e.g., DSA-merged bytemap operands at the SymExpr level).
            if expr.op == "Ite" and len(expr.args) == 3:
                cond = self.eval_expr(expr.args[0])
                return self.eval_expr(expr.args[1] if _as_bool(cond) else expr.args[2])
            return self._eval_apply(expr.op, [self.eval_expr(a) for a in expr.args], expr)
        raise TypeError(f"unsupported expr node: {type(expr).__name__}")

    def _eval_apply(self, op: str, args: list[Value], whole: ApplyExpr) -> Value:
        if op == "Apply" and len(args) >= 2 and isinstance(whole.args[0], SymExpr):
            fn = whole.args[0].name
            if is_known_builtin_function_symbol(fn):
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

    def normalize_symbol(s: str) -> str:
        return canonical_symbol(s, strip_var_suffixes=cfg.strip_var_suffixes)

    store = {normalize_symbol(k): v for k, v in cfg.initial_store.items()}
    memory_store = {normalize_symbol(k): v for k, v in cfg.memory_store.items()}
    symbol_sorts = {normalize_symbol(k): v for k, v in cfg.symbol_sorts.items()}
    model_values = {normalize_symbol(k): v for k, v in cfg.model_values.items()}
    ev = Evaluator(
        store,
        normalize_symbol=normalize_symbol,
        memory_store=memory_store,
        symbol_sorts=symbol_sorts,
        model_values=model_values,
    )
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
                lhs_key = normalize_symbol(cmd.lhs)
                is_bm = ev._is_bytemap_name(cmd.lhs)
                # Compute the symbolic store/load annotation up-front:
                # it only needs the key and val expressions, which can
                # usually be model-evaluated even when the source
                # bytemap's contents are unknown (the common case for
                # production traces — bytemap symbols are huge and
                # rarely fully populated in the model).
                if is_bm:
                    mem_repr = _format_bytemap_store_repr(ev, cmd.rhs)
                else:
                    mem_repr = _format_bytemap_select_reprs(ev, cmd.rhs)
                try:
                    if is_bm:
                        mm = ev._eval_bytemap_expr(cmd.rhs)
                        ev.memory_store[lhs_key] = mm
                        events.append(RunEvent(
                            current, cmd, rendered,
                            note="bytemap update", memory_repr=mem_repr,
                        ))
                    else:
                        val = ev.eval_expr(cmd.rhs)
                        ev.store[lhs_key] = val
                        events.append(RunEvent(
                            current, cmd, rendered,
                            value=val, memory_repr=mem_repr,
                        ))
                except UnknownValueError:
                    if is_bm:
                        # Source map is unknown; drop the LHS so downstream
                        # reads also go Unknown and fall back to the model.
                        # The annotation still surfaces what the program
                        # tried to write and where, which is the only
                        # actionable info for a CEX reader.
                        ev.memory_store.pop(lhs_key, None)
                        events.append(RunEvent(
                            current, cmd, rendered,
                            note="bytemap unknown", memory_repr=mem_repr,
                        ))
                    else:
                        v = ev.model_values.get(lhs_key)
                        if v is not None:
                            ev.store[lhs_key] = v
                            events.append(RunEvent(
                                current, cmd, rendered,
                                value=v, note="from model", memory_repr=mem_repr,
                            ))
                        else:
                            ev.store.pop(lhs_key, None)
                            events.append(RunEvent(current, cmd, rendered, note="unknown"))
                continue

            if isinstance(cmd, AssignHavocCmd):
                lhs_key = normalize_symbol(cmd.lhs)
                if ev._is_bytemap_name(cmd.lhs):
                    # Preserve any model-supplied bytemap; if absent the
                    # name simply stays unknown until something assigns it.
                    events.append(RunEvent(current, cmd, rendered, note="havoc bytemap"))
                    continue
                v = _havoc_value(cmd.lhs, cfg.havoc_mode, cfg.ask_value)
                ev.store[lhs_key] = v
                events.append(RunEvent(current, cmd, rendered, value=v))
                continue

            if isinstance(cmd, AssumeExpCmd):
                try:
                    cond = ev.eval_expr(cmd.condition)
                except UnknownValueError:
                    events.append(RunEvent(current, cmd, rendered, note="cond unknown -> assume"))
                    continue
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
                try:
                    pred = ev.eval_expr(cmd.predicate)
                except UnknownValueError:
                    events.append(RunEvent(current, cmd, rendered, note="inconclusive", color="yellow"))
                    continue
                ok = _as_bool(pred)
                if ok:
                    assert_ok += 1
                    events.append(RunEvent(current, cmd, rendered, note="ok", color="green"))
                else:
                    assert_fail += 1
                    events.append(RunEvent(current, cmd, rendered, note="FAILED (continue)", color="red"))
                continue

            if isinstance(cmd, JumpiCmd):
                cond_txt = canonical_symbol(cmd.condition, strip_var_suffixes=cfg.strip_var_suffixes)
                shown = rendered or f"if {cond_txt} goto {cmd.then_target} else {cmd.else_target}"
                try:
                    cv = ev.get_symbol(cmd.condition)
                    take_then = _as_bool(cv)
                    next_block = cmd.then_target if take_then else cmd.else_target
                    events.append(RunEvent(current, cmd, shown, note=next_block, color="green"))
                except UnknownValueError:
                    next_block = cmd.then_target
                    events.append(
                        RunEvent(current, cmd, shown, note=f"cond unknown -> {next_block}", color="yellow")
                    )
                break

            if isinstance(cmd, JumpCmd):
                next_block = cmd.target
                shown = rendered or f"goto {cmd.target}"
                events.append(RunEvent(current, cmd, shown, note=next_block, color="green"))
                break

            if isinstance(cmd, AnnotationCmd):
                snippet = _parse_snippet_cmd(
                    cmd.payload,
                    weak_is_strong=bool(cmd.strong_refs),
                )
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
                        sym_ref = snippet["symbol"]
                        if isinstance(sym_ref, SymbolWeakRef):
                            v = ev.peek_symbol(sym_ref.name)
                            if v is None:
                                events.append(
                                    RunEvent(
                                        current,
                                        cmd,
                                        f"  {tag}",
                                        note=f"dangling weak use: {sym_ref.name}",
                                        color="yellow",
                                    )
                                )
                            else:
                                events.append(RunEvent(current, cmd, f"  {tag}", value=v, color="cyan"))
                        elif isinstance(sym_ref, SymbolRef):
                            try:
                                v = ev.get_symbol(sym_ref.name)
                            except UnknownValueError:
                                events.append(
                                    RunEvent(
                                        current,
                                        cmd,
                                        f"  {tag}",
                                        note=f"unknown: {sym_ref.name}",
                                        color="yellow",
                                    )
                                )
                            else:
                                events.append(RunEvent(current, cmd, f"  {tag}", value=v, color="cyan"))
                        else:
                            sym = str(sym_ref)
                            v = ev.peek_symbol(sym)
                            if v is None:
                                events.append(
                                    RunEvent(
                                        current,
                                        cmd,
                                        f"  {tag}",
                                        note=f"dangling weak use: {sym}",
                                        color="yellow",
                                    )
                                )
                            else:
                                events.append(RunEvent(current, cmd, f"  {tag}", value=v, color="cyan"))
                        continue
                    if kind == "print_128":
                        tag = str(snippet["tag"])
                        low_ref = snippet["low"]
                        high_ref = snippet["high"]
                        low_is_weak = isinstance(low_ref, SymbolWeakRef)
                        high_is_weak = isinstance(high_ref, SymbolWeakRef)
                        low_name = (
                            low_ref.name
                            if isinstance(low_ref, SymbolRef)
                            else str(low_ref)
                        )
                        high_name = (
                            high_ref.name
                            if isinstance(high_ref, SymbolRef)
                            else str(high_ref)
                        )
                        low: Value | None = None
                        high: Value | None = None
                        try:
                            low = ev.peek_symbol(low_name) if low_is_weak else ev.get_symbol(low_name)
                            high = ev.peek_symbol(high_name) if high_is_weak else ev.get_symbol(high_name)
                        except UnknownValueError as e:
                            events.append(
                                RunEvent(
                                    current,
                                    cmd,
                                    f"  {tag}",
                                    note=f"unknown: {e}",
                                    color="yellow",
                                )
                            )
                            continue
                        if (low_is_weak and low is None) or (high_is_weak and high is None):
                            missing: list[str] = []
                            if low_is_weak and low is None:
                                missing.append(low_name)
                            if high_is_weak and high is None:
                                missing.append(high_name)
                            events.append(
                                RunEvent(
                                    current,
                                    cmd,
                                    f"  {tag}",
                                    note=f"dangling weak use: {', '.join(missing)}",
                                    color="yellow",
                                )
                            )
                        else:
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
