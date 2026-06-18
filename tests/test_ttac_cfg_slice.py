import ttac_fixtures as fx
from ctac.ttac import ast, parse_program
from ctac.ttac.transform.cfg_slice import restrict_to_block


def prog():
    return parse_program(fx.BRANCH_ASSERTS)


def test_keeps_target_and_ancestors_only():
    r = restrict_to_block(prog(), "L")
    assert [b.label for b in r.blocks] == ["entry", "L"]


def test_then_arm_survivor_appends_assume_cond():
    r = restrict_to_block(prog(), "L")
    entry = r.blocks[0]
    assert entry.terminator == ast.Goto("L")
    assert entry.commands[-1] == ast.Assume(ast.Var("c"))


def test_else_arm_survivor_appends_assume_not_cond():
    r = restrict_to_block(prog(), "R")
    entry = r.blocks[0]
    assert entry.terminator == ast.Goto("R")
    assert entry.commands[-1] == ast.Assume(ast.UnExpr("not", ast.Var("c")))


def test_target_block_out_edges_become_sink():
    # L's original `goto exit` leads to a pruned block, so L becomes a sink.
    r = restrict_to_block(prog(), "L")
    live = r.blocks[-1]
    assert live.label == "L"
    assert isinstance(live.terminator, ast.Halt)


def test_single_exit_preserved():
    r = restrict_to_block(prog(), "L")
    from ctac.ttac.transform.cfg_slice import cfg

    g = cfg.to_digraph(r)
    sinks = [n for n in g.nodes if g.out_degree(n) == 0]
    assert sinks == ["L"]
