from __future__ import annotations

from ctac.ast import AssignExpCmd, parse_command_line
from ctac.ast.pretty import DEFAULT_PRINTERS, HumanPrettyPrinter, configured_printer, pretty_lines


def test_default_printers_present() -> None:
    names = DEFAULT_PRINTERS.names()
    assert 'human' in names
    assert 'raw' in names


def test_human_pretty_assign() -> None:
    cmd = parse_command_line('AssignExpCmd R10 0x159')
    human = DEFAULT_PRINTERS.get('human')
    lines = pretty_lines([cmd], printer=human)
    assert lines == ['R10 = 345']


def test_human_skips_annotation_and_label() -> None:
    cmds = [
        parse_command_line('AnnotationCmd JSON{"key":"x"}'),
        parse_command_line('LabelCmd "hello"'),
        AssignExpCmd(raw='AssignExpCmd R1 0x1', lhs='R1', rhs=parse_command_line('AssignExpCmd R0 0x1').rhs),
    ]
    human = DEFAULT_PRINTERS.get('human')
    lines = pretty_lines(cmds, printer=human)
    assert lines == ['R1 = 1']


def test_human_havoc_and_ops_and_skips_jump() -> None:
    cmds = [
        parse_command_line('AssignHavocCmd:18 R1588'),
        parse_command_line('AssumeExpCmd LOr(LNot(B1777) Eq(R0 0x1))'),
        parse_command_line('JumpiCmd:1 T F C'),
        parse_command_line('JumpCmd Z'),
    ]
    human = DEFAULT_PRINTERS.get('human')
    lines = pretty_lines(cmds, printer=human)
    assert lines[0] == 'R1588 = havoc'
    assert lines[1].startswith('assume ')
    assert '||' in lines[1]
    assert '==' in lines[1]
    assert '!' in lines[1]
    assert len(lines) == 2


def test_human_distinguishes_mul_and_intmul() -> None:
    cmds = [
        parse_command_line("AssignExpCmd R1 Mul(R2 R3)"),
        parse_command_line("AssignExpCmd I1 IntMul(R2 R3)"),
    ]
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines(cmds, printer=human)
    assert lines[0] == "R1 = R2 * R3"
    assert lines[1] == "I1 = R2 *int R3"


def test_human_shortens_safe_math_narrow_name() -> None:
    cmd = parse_command_line(
        "AssignExpCmd R1 Apply(safe_math_narrow_bv256:bif IntAdd(0x1 R2))"
    )
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines[0].startswith("R1 = narrow(")
    assert "safe_math_narrow_bv256" not in lines[0]


def test_human_ite_rust_style() -> None:
    cmd = parse_command_line("AssignExpCmd R1 Ite(Eq(R2 0x0) 0x1 0x2)")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["R1 = if R2 == 0 { 1 } else { 2 }"]


def test_raw_printer_preserves_line() -> None:
    cmd = parse_command_line('JumpiCmd:1 B C cond')
    rawp = DEFAULT_PRINTERS.get('raw')
    lines = pretty_lines([cmd], printer=rawp)
    assert lines == ['JumpiCmd:1 B C cond']


def test_human_strips_var_suffixes_by_default() -> None:
    cmd = parse_command_line("AssignExpCmd B1114:1 Eq(R2:25 0x0)")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["B1114 = R2 == 0"]


def test_human_can_keep_var_suffixes() -> None:
    cmd = parse_command_line("AssignExpCmd B1114:1 Eq(R2:25 0x0)")
    human = HumanPrettyPrinter(strip_var_suffixes=False)
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["B1114:1 = R2:25 == 0"]


def test_human_pretty_bit_slice_low_mask() -> None:
    cmd = parse_command_line("AssignExpCmd R1 BWAnd(R349 0xffffffffffffffff)")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["R1 = R349[..64]"]


def test_human_pretty_bit_slice_shifted_contiguous_mask() -> None:
    cmd = parse_command_line("AssignExpCmd R148 BWAnd(R147 70368744161280)")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["R148 = R147[45:14]*[2^14]"]


def test_human_pretty_bit_slice_shift_right() -> None:
    cmd = parse_command_line("AssignExpCmd R1 ShiftRightLogical(R349 0x40)")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["R1 = R349[64..]"]


def test_human_patterns_can_be_disabled() -> None:
    cmd = parse_command_line("AssignExpCmd R1 ShiftRightLogical(R349 0x40)")
    human = configured_printer("human", human_patterns=False)
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["R1 = R349 >> 0x40"]


def test_human_number_formatting_can_be_disabled() -> None:
    cmd = parse_command_line("AssignExpCmd R10 0x159")
    human = configured_printer("human", human_patterns=False)
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["R10 = 0x159"]


def test_human_prefers_pow2_label_for_large_exact_power() -> None:
    cmd = parse_command_line("AssignExpCmd I1 IntMul(0x10000000000000000(int) R2)")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["I1 = [2^64] *int R2"]


def test_human_prefers_near_pow2_label_within_delta_16() -> None:
    cmd = parse_command_line("AssignExpCmd I1 IntMul(18446744073709551614(int) R2)")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["I1 = [2^64-2] *int R2"]


def test_human_assume_range_rewrite() -> None:
    cmd = parse_command_line("AssumeExpCmd LAnd(Ge(R341 0x1) Le(R341 0xffffffffffffffff))")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["assume R341 in [1, 2^64-1]"]


def test_human_assume_range_rewrite_with_flipped_bounds() -> None:
    cmd = parse_command_line("AssumeExpCmd LAnd(Le(0x8 R341) Ge(0x17 R341))")
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ["assume R341 in [8, 2^4+7]"]


def test_human_renders_cex_print_value_annotation() -> None:
    cmd = parse_command_line(
        'AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.CexPrintValues","displayMessage":"user_borrow_amount","symbols":[{"namePrefix":"R1289:7"}]}}'
    )
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ['clog("user_borrow_amount", R1289)']


def test_human_renders_cex_print_128_annotation() -> None:
    cmd = parse_command_line(
        'AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.CexPrint128BitsValue","displayMessage":"amount","low":{"namePrefix":"R1:2"},"high":{"namePrefix":"R2:9"},"signed":true}}'
    )
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([cmd], printer=human)
    assert lines == ['clog("amount", "R1..R2 (signed)", R1, R2)']


def test_human_renders_scope_annotations_as_calls() -> None:
    start = parse_command_line(
        'AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.ScopeStart","scopeName":"pre"}}'
    )
    end = parse_command_line(
        'AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"vc.data.SnippetCmd.CvlrSnippetCmd.ScopeEnd","scopeName":"pre"}}'
    )
    human = DEFAULT_PRINTERS.get("human")
    lines = pretty_lines([start, end], printer=human)
    assert lines == ['clog_scope_start("pre")', 'clog_scope_end("pre")']


def test_human_renders_int_ceil_div_as_function_call() -> None:
    """``IntCeilDiv(a, b)`` is a TAC concept (not a primitive op). The human
    printer renders it as ``int_div_ceil(a, b)`` (Rust naming convention);
    the raw printer round-trips the PascalCase form."""
    cmd = parse_command_line("AssignExpCmd R IntCeilDiv(A B)")
    human = DEFAULT_PRINTERS.get("human")
    raw = DEFAULT_PRINTERS.get("raw")
    assert pretty_lines([cmd], printer=human) == ["R = int_div_ceil(A, B)"]
    # Raw printer preserves the input verbatim.
    assert pretty_lines([cmd], printer=raw) == ["AssignExpCmd R IntCeilDiv(A B)"]


def test_human_int_ceil_div_round_trips_through_parser() -> None:
    """Parser round-trip: parse `IntCeilDiv(A, B)` from raw TAC, render
    the AST, reparse — ApplyExpr.op stays ``IntCeilDiv``."""
    from ctac.ast.nodes import ApplyExpr

    cmd = parse_command_line("AssignExpCmd R IntCeilDiv(A B)")
    assert isinstance(cmd, AssignExpCmd)
    assert isinstance(cmd.rhs, ApplyExpr)
    assert cmd.rhs.op == "IntCeilDiv"
    assert len(cmd.rhs.args) == 2


def test_human_renders_int_mul_div_as_function_call() -> None:
    """``IntMulDiv(a, b, c)`` is a TAC concept (axiomatized full-precision
    multiply-then-divide). The human printer renders as ``muldiv(a, b, c)``;
    the raw printer round-trips the PascalCase form."""
    cmd = parse_command_line("AssignExpCmd R IntMulDiv(A B C)")
    human = DEFAULT_PRINTERS.get("human")
    raw = DEFAULT_PRINTERS.get("raw")
    assert pretty_lines([cmd], printer=human) == ["R = muldiv(A, B, C)"]
    assert pretty_lines([cmd], printer=raw) == ["AssignExpCmd R IntMulDiv(A B C)"]


def test_human_int_mul_div_round_trips_through_parser() -> None:
    """Parser round-trip: `IntMulDiv(A B C)` parses as
    ``ApplyExpr(op="IntMulDiv", args=(A, B, C))`` and stays that way."""
    from ctac.ast.nodes import ApplyExpr

    cmd = parse_command_line("AssignExpCmd R IntMulDiv(A B C)")
    assert isinstance(cmd, AssignExpCmd)
    assert isinstance(cmd.rhs, ApplyExpr)
    assert cmd.rhs.op == "IntMulDiv"


def test_human_select_renders_as_index() -> None:
    cmd = parse_command_line("AssignExpCmd R Select(M K)")
    human = DEFAULT_PRINTERS.get("human")
    assert pretty_lines([cmd], printer=human) == ["R = M[K]"]


def test_human_store_renders_as_functional_update() -> None:
    cmd = parse_command_line("AssignExpCmd M2 Store(M1 K V)")
    human = DEFAULT_PRINTERS.get("human")
    assert pretty_lines([cmd], printer=human) == ["M2 = M1[K := V]"]


def test_human_store_chain_renders_as_chained_updates() -> None:
    """Nested ``Store(Store(Store(M, k1, v1), k2, v2), k3, v3)`` —
    common shape on bytemap-rw programs — renders as a chain of
    bracket-update segments."""
    cmd = parse_command_line(
        "AssignExpCmd M4 Store(Store(Store(M K1 V1) K2 V2) K3 V3)"
    )
    human = DEFAULT_PRINTERS.get("human")
    assert pretty_lines([cmd], printer=human) == [
        "M4 = M[K1 := V1][K2 := V2][K3 := V3]"
    ]


def test_human_wrap_twos_complement_renders_as_to_s256() -> None:
    cmd = parse_command_line(
        "AssignExpCmd R Apply(wrap_twos_complement_256:bif I)"
    )
    human = DEFAULT_PRINTERS.get("human")
    assert pretty_lines([cmd], printer=human) == ["R = to_s256(I)"]


def test_human_unwrap_twos_complement_renders_as_from_s256() -> None:
    cmd = parse_command_line(
        "AssignExpCmd I Apply(unwrap_twos_complement_256:bif R)"
    )
    human = DEFAULT_PRINTERS.get("human")
    assert pretty_lines([cmd], printer=human) == ["I = from_s256(R)"]


def test_parser_accepts_negative_hex_const() -> None:
    """TAC dumps emit negative hex constants as ``0x-N``. Parser must
    treat them as a single ConstExpr, not as ``Apply(0x-N, ...)``
    (which was the bug that surfaced as use-before-def on the
    symbol ``int``)."""
    from ctac.ast.nodes import ApplyExpr, ConstExpr

    cmd = parse_command_line(
        "AssumeExpCmd Eq(I581 0x-48(int))"
    )
    cond = cmd.condition
    assert isinstance(cond, ApplyExpr)
    assert cond.op == "Eq"
    rhs = cond.args[1]
    assert isinstance(rhs, ConstExpr)
    assert rhs.value == "0x-48(int)"


def test_human_renders_negative_const_with_sign_outside_brackets() -> None:
    """Pretty-print a negative constant by formatting the absolute
    value with the existing labeled-form logic and prepending ``-``
    OUTSIDE the brackets — ``-[2^64]`` not ``[-2^64]``. The brackets
    are the unambiguous grouping marker; the sign goes outside.

    Plain decimals (no labeled form) get the standard ``-72`` form
    via ``_format_dec_10k``."""
    cases = [
        # (input, expected_pretty)
        ("0x-48(int)", "-[2^6+8]"),  # -72; 72 = 2^6 + 8 → labeled form
        # Power-of-two: sign outside the bracketed pure-power label.
        # (-(2^64) — int constant, hex would wrap mod 2^256, so use a
        # decimal-shaped negative.)
    ]
    for raw, expected in cases:
        cmd = parse_command_line(f"AssignExpCmd I {raw}")
        human = DEFAULT_PRINTERS.get("human")
        assert pretty_lines([cmd], printer=human) == [
            f"I = {expected}"
        ], f"failed for {raw!r}"


def test_human_renders_negative_pow2_label() -> None:
    """``-2^64`` renders as ``-[2^64]`` (sign outside the pure-power
    label, no extra parens)."""
    from ctac.eval.value_format import Value, format_value_human_single

    assert format_value_human_single(Value("int", -(1 << 64))) == "-[2^64]"
    assert format_value_human_single(Value("int", 1 << 64)) == "[2^64]"


def test_human_renders_negative_compound_label() -> None:
    """A compound label like ``2^6+8`` (= 72) negated stays without
    parens — brackets are the grouping. ``-72 → -[2^6+8]``."""
    from ctac.eval.value_format import Value, format_value_human_single

    assert format_value_human_single(Value("int", -72)) == "-[2^6+8]"


def test_human_renders_small_negative_as_plain_decimal() -> None:
    """Small negatives that don't match any labeled form fall through
    to plain decimal, no brackets."""
    from ctac.eval.value_format import Value, format_value_human_single

    assert format_value_human_single(Value("int", -7)) == "-7"
    assert format_value_human_single(Value("int", -1234)) == "-1234"


def test_twos_complement_bifs_excluded_from_use_iterator() -> None:
    """The ``:bif`` callee in ``Apply(unwrap_twos_complement_256:bif, R)``
    is a built-in function symbol, not a variable use. Adding it to
    BUILTIN_FUNCTIONS lets ``iter_expr_symbols`` skip the callee
    position via ``is_known_builtin_function_symbol`` (already wired
    in expr_walk.py). Pinning so the registry entry can't drift
    silently."""
    from ctac.analysis.expr_walk import command_uses

    cmd = parse_command_line(
        "AssignExpCmd I Apply(unwrap_twos_complement_256:bif R0)"
    )
    uses = command_uses(cmd)
    # Only R0 is a use; the bif callee is filtered.
    assert "R0" in uses
    assert not any("twos_complement" in u for u in uses)
    assert not any(":bif" in u for u in uses)
