"""Pluggable pretty printers for TAC command AST."""

from __future__ import annotations

import json
import re
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Protocol

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
    SymbolRef,
    SymbolWeakRef,
    TacCmd,
    TacExpr,
)
from ctac.ast.bit_mask import shifted_contiguous_mask
from ctac.ast.range_constraints import match_inclusive_range_constraint
from ctac.ast.visitor import TacVisitor
from ctac.builtins import pretty_builtin_name
from ctac.eval.value_format import format_const_token_human


class CommandPrinter(Protocol):
    name: str

    def print_expr(self, expr: TacExpr) -> str: ...

    def print_cmd(self, cmd: TacCmd) -> str | None: ...


class PrettyPrinter(TacVisitor):
    """Base class for one concrete pretty-print style."""

    name = 'base'

    def __init__(self, *, strip_var_suffixes: bool = True) -> None:
        self.strip_var_suffixes = strip_var_suffixes

    @staticmethod
    def _strip_var_suffix(tok: str) -> str:
        # TAC variables/symbols often carry meta suffixes like `:1`, `:25`, `:0`.
        # Keep this optional, because raw/debug views may prefer the original token.
        return re.sub(r":\d+$", "", tok)

    def _fmt_symbol_token(self, tok: str) -> str:
        if self.strip_var_suffixes:
            return self._strip_var_suffix(tok)
        return tok

    @staticmethod
    def _strip_outer_parens_once(s: str) -> str:
        """
        Remove one surrounding pair of parentheses if they wrap the whole string.

        Example: ``(a + b)`` -> ``a + b``; ``(a) + (b)`` stays unchanged.
        """
        s = s.strip()
        if len(s) < 2 or s[0] != "(" or s[-1] != ")":
            return s
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    return s
        return s[1:-1].strip()

    def print_expr(self, expr: TacExpr) -> str:
        return self.visit(expr)

    def print_cmd(self, cmd: TacCmd) -> str | None:
        return self.visit(cmd)

    # expressions
    def visit_SymbolRef(self, node: SymbolRef) -> str:
        return self._fmt_symbol_token(node.name)

    def visit_SymbolWeakRef(self, node: SymbolWeakRef) -> str:
        return self._fmt_symbol_token(node.name)

    def visit_ConstExpr(self, node: ConstExpr) -> str:
        return node.value

    def visit_ApplyExpr(self, node: ApplyExpr) -> str:
        args = ', '.join(self.print_expr(a) for a in node.args)
        return f"{node.op}({args})"

    # commands defaults
    def visit_AssignExpCmd(self, node: AssignExpCmd) -> str:
        rhs = self._strip_outer_parens_once(self.print_expr(node.rhs))
        return f"{self._fmt_symbol_token(node.lhs)} = {rhs}"

    def visit_AssumeExpCmd(self, node: AssumeExpCmd) -> str:
        cond = self._strip_outer_parens_once(self.print_expr(node.condition))
        return f"assume {cond}"

    def visit_JumpCmd(self, node: JumpCmd) -> str:
        return f"goto {node.target}"

    def visit_JumpiCmd(self, node: JumpiCmd) -> str:
        cond = self._fmt_symbol_token(node.condition)
        return f"if {cond} goto {node.then_target} else {node.else_target}"

    def visit_AssertCmd(self, node: AssertCmd) -> str:
        pred = self._strip_outer_parens_once(self.print_expr(node.predicate))
        if node.message:
            return f"assert {pred}  # {node.message}"
        return f"assert {pred}"

    def visit_LabelCmd(self, node: LabelCmd) -> str | None:
        return None

    def visit_AnnotationCmd(self, node: AnnotationCmd) -> str | None:
        return None

    def visit_RawCmd(self, node: RawCmd) -> str:
        return node.raw


class HumanPrettyPrinter(PrettyPrinter):
    """Default human printer; skips labels/annotations by design."""

    name = 'human'

    def __init__(self, *, strip_var_suffixes: bool = True, human_patterns: bool = True) -> None:
        super().__init__(strip_var_suffixes=strip_var_suffixes)
        self.human_patterns = human_patterns
        # Optional block-id back-mapping used to annotate rw-eq's
        # DEST_<bid> / IN_DEST_<bid> integer constants with the source
        # block id. Populated from a top-of-program ``rw-eq.id-of``
        # annotation (see ``visit_AnnotationCmd``). When ``None`` the
        # printer behaves identically to before.
        self._id_to_block: dict[int, str] | None = None

    _binary_infix = {
        "Eq": "==",
        "Lt": "<",
        "Le": "<=",
        "Gt": ">",
        "Ge": ">=",
        "Slt": "<s",
        "Sle": "<=s",
        "Sgt": ">s",
        "Sge": ">=s",
        "LAnd": "&&",
        "LOr": "||",
        "BWAnd": "&",
        "BWOr": "|",
        "BWXOr": "^",
        "Add": "+",
        "IntAdd": "+int",
        "Sub": "-",
        "IntSub": "-int",
        "Mul": "*",
        "IntMul": "*int",
        "Div": "/",
        "IntDiv": "/int",
        "Mod": "%",
        "IntMod": "%int",
        "ShiftLeft": "<<",
        "ShiftRightLogical": ">>",
        "ShiftRightArithmetical": ">>s",
    }

    _unary_prefix = {
        "LNot": "!",
        "BWNot": "~",
    }

    # Function-call-style rendering (snake_case) for TAC ops that are
    # axiomatized concepts rather than primitive operations. The raw TAC
    # name (PascalCase, e.g. ``IntCeilDiv``) round-trips unchanged; only
    # the human printer remaps to a snake_case alias.
    _int_func_remap = {
        "IntCeilDiv": "div_ceil",
        "IntMulDiv": "muldiv",
        "IntMulDivCeil": "muldiv_ceil",
    }

    @staticmethod
    def _const_to_int(expr: TacExpr) -> int | None:
        if not isinstance(expr, ConstExpr):
            return None
        tok = expr.value.strip()
        if tok.endswith(")") and "(" in tok:
            lp = tok.rfind("(")
            rp = tok.rfind(")")
            if rp == len(tok) - 1 and lp > 0:
                tok = tok[:lp]
        tok = tok.replace("_", "")
        try:
            if tok.startswith(("0x", "0X")):
                return int(tok, 16)
            return int(tok, 10)
        except ValueError:
            return None

    def _bit_slice_low_mask(self, node: ApplyExpr) -> str | None:
        if node.op != "BWAnd" or len(node.args) != 2:
            return None
        lhs, rhs = node.args
        sym: SymExpr | None = None
        mask: int | None = None
        if isinstance(lhs, SymExpr):
            sym = lhs
            mask = self._const_to_int(rhs)
        elif isinstance(rhs, SymExpr):
            sym = rhs
            mask = self._const_to_int(lhs)
        if sym is None or mask is None or mask <= 0:
            return None
        # Match mask = 2^k - 1; then print Rust-style [..k] (end-exclusive).
        bit_width = mask.bit_length()
        if mask != (1 << bit_width) - 1:
            return None
        return f"{self._fmt_symbol_token(sym.name)}[..{bit_width}]"

    def _bit_slice_shifted_contiguous_mask(self, node: ApplyExpr) -> str | None:
        if node.op != "BWAnd" or len(node.args) != 2:
            return None
        lhs, rhs = node.args
        sym: SymExpr | None = None
        mask: int | None = None
        if isinstance(lhs, SymExpr):
            sym = lhs
            mask = self._const_to_int(rhs)
        elif isinstance(rhs, SymExpr):
            sym = rhs
            mask = self._const_to_int(lhs)
        if sym is None or mask is None or mask <= 0:
            return None
        sw = shifted_contiguous_mask(mask)
        if sw is None:
            return None
        lo, w = sw
        if lo == 0:
            return None
        hi = lo + w - 1
        # Show extract (slice) then re-align: (x >> lo) & width mask, shifted back by 2^lo.
        return f"{self._fmt_symbol_token(sym.name)}[{hi}:{lo}]*[2^{lo}]"

    def _bit_slice_shift_right(self, node: ApplyExpr) -> str | None:
        if node.op != "ShiftRightLogical" or len(node.args) != 2:
            return None
        lhs, rhs = node.args
        if not isinstance(lhs, SymExpr):
            return None
        shift = self._const_to_int(rhs)
        if shift is None or shift < 0:
            return None
        # Rust-style [k..] (start-inclusive, open-ended).
        return f"{self._fmt_symbol_token(lhs.name)}[{shift}..]"

    def _short_fn_name(self, fn: str) -> str:
        # Map known TAC builtins to compact names.
        return pretty_builtin_name(fn)

    @staticmethod
    def _unbracket_label(s: str) -> str:
        t = s.strip()
        if len(t) >= 3 and t.startswith("[") and t.endswith("]"):
            return t[1:-1]
        return t

    def _format_bound_expr(self, expr: TacExpr) -> str:
        if isinstance(expr, ConstExpr):
            return self._unbracket_label(format_const_token_human(expr.value))
        return self._strip_outer_parens_once(self.print_expr(expr))

    def visit_ConstExpr(self, node: ConstExpr) -> str:
        if not self.human_patterns:
            return super().visit_ConstExpr(node)
        return format_const_token_human(node.value)

    def visit_ApplyExpr(self, node: ApplyExpr) -> str:
        if self.human_patterns:
            masked = self._bit_slice_low_mask(node)
            if masked is not None:
                return masked
            shifted_mask = self._bit_slice_shifted_contiguous_mask(node)
            if shifted_mask is not None:
                return shifted_mask
            shifted = self._bit_slice_shift_right(node)
            if shifted is not None:
                return shifted

        op = node.op
        args = [self.print_expr(a) for a in node.args]

        if op in self._unary_prefix and len(args) == 1:
            return f"{self._unary_prefix[op]}({args[0]})"

        if op == "Ite" and len(args) == 3:
            # Rust-like conditional expression form.
            cond = self._strip_outer_parens_once(args[0])
            return f"(if {cond} {{ {args[1]} }} else {{ {args[2]} }})"

        if op == "Select" and len(args) == 2:
            return f"{args[0]}[{args[1]}]"

        if op == "Store" and len(args) == 3:
            # Functional update: returns a new map equal to args[0]
            # except at args[1], where it's args[2]. Renders well in
            # the common nested-Store chain (each segment chains).
            return f"{args[0]}[{args[1]} := {args[2]}]"

        if op in self._binary_infix and len(args) >= 2:
            inf = self._binary_infix[op]
            return "(" + f" {inf} ".join(args) + ")"

        if op in self._int_func_remap:
            fn = self._int_func_remap[op]
            rest = ", ".join(self._strip_outer_parens_once(a) for a in args)
            return f"{fn}({rest})"

        if op == "Apply" and args:
            fn = self._short_fn_name(args[0])
            rest = ", ".join(args[1:])
            return f"{fn}({rest})"

        return super().visit_ApplyExpr(node)

    def visit_AssignHavocCmd(self, node: AssignHavocCmd) -> str:
        return f"{self._fmt_symbol_token(node.lhs)} = havoc"

    # SBF-style inline /* ... */ comments don't carry user-visible
    # information that survives the parser; raw mode keeps them, human
    # mode strips them from RawCmd lines so call/store shapes don't
    # render with debug metadata trailing.
    _INLINE_COMMENT_RE = re.compile(r"\s*/\*.*?\*/")
    # Each /*...*/ comment, captured without the surrounding markers.
    _COMMENT_BODY_RE = re.compile(r"/\*\s*(.*?)\s*\*/")
    # Bytecode address comments (e.g. `/* 0xb728 */`) — recognised so
    # we can skip them when looking for the bare name annotation.
    _HEX_ADDR_RE = re.compile(r"^0[xX][0-9a-fA-F]+$")
    # SBF inlining scaffolding: `call CVT_save_scratch_registers` opens
    # an inlined scope, the matching `CVT_restore_scratch_registers`
    # closes it. The name + call_id come from the call's inline
    # metadata comments (`/*inlined_function_name=...*/`,
    # `/*call_id=N*/`, or a bare `/*<helper_name>*/` for promoted
    # helpers like `promoted_memcpy_zext`).
    _INLINE_SCOPE_OPEN = "CVT_save_scratch_registers"
    _INLINE_SCOPE_CLOSE = "CVT_restore_scratch_registers"

    @classmethod
    def _parse_inline_metadata(cls, raw: str) -> tuple[str | None, str | None]:
        """Return ``(name, call_id)`` parsed from a CVT_{save,restore}
        call's inline ``/*...*/`` comments. Either may be None if
        absent.

        The name is taken from ``inlined_function_name=...`` when
        present (full Rust path), otherwise from the first bare
        comment that isn't a bytecode address or another known
        ``key=value`` annotation (covers promoted helpers like
        ``promoted_memcpy_zext`` whose name appears as a bare tag).
        """
        name: str | None = None
        bare_name: str | None = None
        call_id: str | None = None
        for body in cls._COMMENT_BODY_RE.findall(raw):
            if body.startswith("inlined_function_name="):
                name = body[len("inlined_function_name="):]
                continue
            if body.startswith("call_id="):
                call_id = body[len("call_id="):]
                continue
            if body.startswith("inlined_function_size="):
                continue
            if cls._HEX_ADDR_RE.match(body):
                continue
            if "=" in body:
                # Some other key=value annotation we don't care about.
                continue
            if bare_name is None:
                bare_name = body
        return (name or bare_name), call_id

    def visit_RawCmd(self, node: RawCmd) -> str:
        # Reconstruct the SBF call/callx/exit shapes from the parsed
        # head + tail rather than `node.raw` (which carries inline
        # comments). Falling back to `tail` for other RawCmd shapes
        # gives the comment-and-type-stripped core text the SBF
        # parser computed; for TAC RawCmds (no inline comments)
        # tail is identical to the meaningful part of raw.
        if node.head == "CallCmd":
            verb = (
                "enter" if node.tail == self._INLINE_SCOPE_OPEN
                else "leave" if node.tail == self._INLINE_SCOPE_CLOSE
                else None
            )
            if verb is not None:
                name, cid = self._parse_inline_metadata(node.raw)
                if name is not None:
                    cid_part = f" id:{cid}" if cid is not None else ""
                    return f"{verb} {name}{cid_part}"
                # No metadata to ground the marker — fall through to
                # the literal call rendering rather than emit a
                # half-broken `enter ?` line.
            return f"call {node.tail}"
        if node.head == "CallxCmd":
            return f"callx {node.tail}"
        if node.head == "ExitCmd":
            return "exit"
        if node.tail:
            return node.tail
        return self._INLINE_COMMENT_RE.sub("", node.raw).rstrip() or node.raw

    def visit_AssumeExpCmd(self, node: AssumeExpCmd) -> str:
        if self.human_patterns:
            rng = match_inclusive_range_constraint(
                node.condition,
                strip_var_suffixes=self.strip_var_suffixes,
            )
            if rng is not None:
                var_txt = self._fmt_symbol_token(rng.symbol)
                lo_txt = self._format_bound_expr(rng.lower)
                hi_txt = self._format_bound_expr(rng.upper)
                return f"assume {var_txt} in [{lo_txt}, {hi_txt}]"
        return super().visit_AssumeExpCmd(node)

    def _format_warning_line(self, key: dict, val: dict) -> str | None:
        # Warnings are debug-snippet annotations whose `value.msg` starts
        # with "Warning". They flag soundness-relevant over-approximations
        # (e.g. pointer-analysis split/merge) that can produce spurious
        # counterexamples and are crucial for debugging — so the human
        # printer must surface them rather than swallow the annotation.
        msg = val.get("msg")
        if not isinstance(msg, str):
            return None
        if not msg.lstrip().lower().startswith("warning"):
            return None
        name = key.get("name")
        name_part = f" [{name}]" if isinstance(name, str) else ""
        syms = val.get("symbols")
        sym_tokens: list[str] = []
        if isinstance(syms, list):
            for ent in syms:
                if isinstance(ent, dict):
                    p = ent.get("namePrefix")
                    if isinstance(p, str):
                        sym_tokens.append(self._fmt_symbol_token(p))
        sym_part = f" ({', '.join(sym_tokens)})" if sym_tokens else ""
        return f"!!! WARNING{name_part}: {msg}{sym_part}"

    def visit_AnnotationCmd(self, node: AnnotationCmd) -> str | None:
        payload = node.payload.strip()
        if not payload.startswith("JSON"):
            return None
        try:
            obj = json.loads(payload[4:])
        except json.JSONDecodeError:
            return None
        if not isinstance(obj, dict):
            return None
        key = obj.get("key")
        val = obj.get("value")
        if not isinstance(key, dict) or not isinstance(val, dict):
            return None
        # rw-eq's stuttering walker stashes the id_of mapping (int →
        # block id, used by DEST/IN_DEST constants) here so downstream
        # printers can render it inline. Consume it: populate state,
        # suppress from output.
        if key.get("name") == "rw-eq.id-of":
            mapping: dict[int, str] = {}
            for k, v in val.items():
                if isinstance(k, str) and isinstance(v, str):
                    try:
                        mapping[int(k)] = v
                    except ValueError:
                        continue
            if mapping:
                self._id_to_block = mapping
            return None
        warn = self._format_warning_line(key, val)
        if warn is not None:
            return warn
        if key.get("name") != "snippet.cmd":
            return None
        klass = val.get("#class")
        if not isinstance(klass, str):
            return None

        if klass.endswith(".ScopeStart"):
            scope = val.get("scopeName")
            if isinstance(scope, str):
                return f"clog_scope_start({json.dumps(scope)})"
            return None

        if klass.endswith(".ScopeEnd"):
            scope = val.get("scopeName")
            if isinstance(scope, str):
                return f"clog_scope_end({json.dumps(scope)})"
            return "clog_scope_end()"

        if klass.endswith(".CexPrintValues"):
            msg = val.get("displayMessage")
            syms = val.get("symbols")
            if not isinstance(msg, str) or not isinstance(syms, list) or not syms:
                return None
            regs: list[str] = []
            for ent in syms:
                if not isinstance(ent, dict):
                    continue
                reg = ent.get("namePrefix")
                if isinstance(reg, str):
                    regs.append(self._fmt_symbol_token(reg))
            if not regs:
                return None
            msg_q = json.dumps(msg)
            reg_args = ", ".join(regs)
            return f"clog({msg_q}, {reg_args})"

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
            msg_q = json.dumps(msg)
            low_txt = self._fmt_symbol_token(low_sym)
            high_txt = self._fmt_symbol_token(high_sym)
            if signed:
                return f'clog({msg_q}, "{low_txt}..{high_txt} (signed)", {low_txt}, {high_txt})'
            return f'clog({msg_q}, "{low_txt}..{high_txt}", {low_txt}, {high_txt})'

        if klass.endswith(".CexPrintTag"):
            msg = val.get("displayMessage")
            if isinstance(msg, str):
                return f"clog({json.dumps(msg)})"
            return None

        return None

    def visit_JumpCmd(self, node: JumpCmd) -> str | None:
        # Block terminator is rendered from CFG successors in `pp`.
        return None

    def visit_JumpiCmd(self, node: JumpiCmd) -> str | None:
        # Block terminator is rendered from CFG successors in `pp`.
        return None

    def visit_AssignExpCmd(self, node: AssignExpCmd) -> str:
        line = super().visit_AssignExpCmd(node)
        # Annotate rw-eq's DEST_<bid> / IN_DEST_<bid> assignments with
        # the block-id back-mapping for each integer constant in the
        # rhs. Requires the ``rw-eq.id-of`` annotation to have been
        # seen earlier (sets ``self._id_to_block``).
        if self._id_to_block is None:
            return line
        if not (node.lhs.startswith("DEST_") or node.lhs.startswith("IN_DEST_")):
            return line
        pairs = self._collect_id_constants(node.rhs)
        if not pairs:
            return line
        annot = ", ".join(f"{n} → {bid}" for n, bid in pairs)
        return f"{line}  # {annot}"

    def _collect_id_constants(
        self, expr: TacExpr
    ) -> list[tuple[int, str]]:
        """Walk ``expr`` collecting (int_value, block_id) pairs for any
        ``ConstExpr`` whose integer value is a key in ``_id_to_block``.
        Order is left-to-right traversal; duplicates removed while
        preserving first-seen order."""
        if self._id_to_block is None:
            return []
        seen: set[int] = set()
        out: list[tuple[int, str]] = []
        stack: list[TacExpr] = [expr]
        while stack:
            cur = stack.pop()
            if isinstance(cur, ConstExpr):
                n = self._const_to_int(cur)
                if n is not None and n in self._id_to_block and n not in seen:
                    seen.add(n)
                    out.append((n, self._id_to_block[n]))
            elif isinstance(cur, ApplyExpr):
                stack.extend(reversed(cur.args))
        return out


class RawPrettyPrinter(PrettyPrinter):
    """Printer that preserves command lines exactly as in dump."""

    name = 'raw'

    def print_expr(self, expr: TacExpr) -> str:
        return super().print_expr(expr)

    def print_cmd(self, cmd: TacCmd) -> str | None:
        return cmd.raw


@dataclass
class PrinterRegistry:
    _printers: dict[str, CommandPrinter]

    @classmethod
    def with_defaults(cls) -> 'PrinterRegistry':
        reg = cls({})
        reg.register(HumanPrettyPrinter())
        reg.register(RawPrettyPrinter())
        return reg

    def register(self, p: CommandPrinter) -> None:
        self._printers[p.name] = p

    def names(self) -> list[str]:
        return sorted(self._printers)

    def get(self, name: str) -> CommandPrinter:
        if name not in self._printers:
            raise KeyError(f"unknown pretty-printer {name!r}; choose one of: {', '.join(self.names())}")
        return self._printers[name]


DEFAULT_PRINTERS = PrinterRegistry.with_defaults()


def configured_printer(
    name: str,
    *,
    strip_var_suffixes: bool = True,
    human_patterns: bool = True,
) -> CommandPrinter:
    """Instantiate a configurable printer by name from defaults registry."""
    if name == "human":
        return HumanPrettyPrinter(
            strip_var_suffixes=strip_var_suffixes,
            human_patterns=human_patterns,
        )
    if name == "raw":
        # Raw printer intentionally preserves `cmd.raw` exactly.
        return RawPrettyPrinter(strip_var_suffixes=strip_var_suffixes)
    return DEFAULT_PRINTERS.get(name)


def pretty_lines(cmds: Iterable[TacCmd], *, printer: CommandPrinter) -> list[str]:
    out: list[str] = []
    for c in cmds:
        line = printer.print_cmd(c)
        if line is not None and line != '':
            out.append(line)
    return out
