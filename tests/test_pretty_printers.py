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
