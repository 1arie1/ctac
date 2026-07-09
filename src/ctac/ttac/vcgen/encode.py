"""Seahorn-style VC generation for TinyTAC.

Reuses the ctac VCGen library (``ctac.smt.vc``: ``VCBuilder`` + operator
model + UF bytemap), the CFG-encoding library (``ctac.smt.cfg``), and
renders to SMT-LIB. The seahorn VC is ``CFG and DEF and JUMPS and PHI
and ERROR`` over per-block reachability vars: ``CFG``/``JUMPS`` come from
the reused CFG encoder, ``DEF``/``PHI``/``ERROR`` from the ttac walk.
DSA dynamic defs need no special path --- each definition emits a
block-guarded equality and the CFG encoder's at-most-one over
predecessors selects one.
"""

from __future__ import annotations

from dataclasses import dataclass

import networkx as nx

from ctac.smt.cfg import CFG_ENCODERS, CfgEdge, CfgEmit, CfgEncodeInput
from ctac.smt.vc.builder import VCBuilder, sanitize_name
from ctac.smt.vc.config import BytemapConfig, VCConfig
from ctac.smt.vc.script import VCScript, render_vc_script
from ctac.smt.vc.terms import Bool, Int, Term, app, not_, true

from ctac.ttac import ast
from ctac.ttac.analysis import cfg as ttac_cfg
from ctac.ttac.analysis import check_dsa, infer_types
from ctac.ttac.ast import Ty
from ctac.ttac.errors import VcGenError
from ctac.ttac.transform import merge_asserts

from .gamma import GammaPlan, encoder_atoms, plan_gammas, term_to_smt, tgamma_rhs_term
from .lower import TtacLowerer

_TY_TO_SORT_NAME = {Ty.INT: "int", Ty.BOOL: "bool", Ty.BYTEMAP: "bytemap"}


@dataclass(frozen=True)
class VcResult:
    script: VCScript
    smt_text: str
    assert_block: str
    asserts_before: int
    merged: bool
    gamma_sites: int = 0


def _assert_sites(program: ast.Program) -> list[tuple[str, int, str]]:
    return [
        (b.label, i, c.cond_name)
        for b in program.blocks
        for i, c in enumerate(b.commands)
        if isinstance(c, ast.Assert)
    ]


def generate_vc(
    program: ast.Program, *, cfg_encoding: str = "bwd0", merge: str = "phi"
) -> VcResult:
    if merge not in ("phi", "gamma"):
        raise VcGenError(f"unknown merge mode {merge!r}; available: phi, gamma")
    return _generate_vc(program, cfg_encoding=cfg_encoding, merge=merge)


def _generate_vc(program: ast.Program, *, cfg_encoding: str, merge: str) -> VcResult:
    sites = _assert_sites(program)
    if not sites:
        raise VcGenError("no assertion to verify")
    asserts_before = len(sites)
    merged = False
    if len(sites) > 1:
        program = merge_asserts(program).program
        merged = True
        sites = _assert_sites(program)

    if not nx.is_directed_acyclic_graph(ttac_cfg.to_digraph(program)):
        raise VcGenError("program has a loop; vcgen requires a loop-free CFG")

    dsa = check_dsa(program)
    if not dsa.is_valid:
        detail = "; ".join(i.detail for i in dsa.issues)
        raise VcGenError(f"program is not in DSA/SSA form: {detail}")

    types = infer_types(program)  # raises TtacTypeError if not total
    symbol_sorts: dict[str, str] = {}
    for name, ty in types.items():
        if ty == Ty.REF:
            raise VcGenError(
                f"variable {name!r} has reference type; desugar references before vcgen"
            )
        symbol_sorts[name] = _TY_TO_SORT_NAME[ty]
    for name in dsa.dynamic:
        if symbol_sorts.get(name) == "bytemap":
            raise VcGenError(
                f"bytemap {name!r} has dynamic (multi-block) definitions; "
                "not supported by vcgen v1"
            )

    assert_block, _assert_idx, assert_cond = sites[0]

    vc = VCBuilder(VCConfig(logic="QF_UFNIA", bytemap=BytemapConfig(select_range="none")))
    lower = TtacLowerer(vc, symbol_sorts)
    entry = program.entry

    def guard(label: str) -> Term:
        if label == entry:
            return true()
        return vc.const("BLK_" + sanitize_name(label), Bool)

    gamma_plan = plan_gammas(program, types) if merge == "gamma" else GammaPlan()

    for block in program.blocks:
        with vc.block(block.label, guard=guard(block.label)) as b:
            for i, cmd in enumerate(block.commands):
                if (block.label, i) in gamma_plan.sites:
                    _emit_gamma(vc, lower, program, symbol_sorts, gamma_plan,
                                block.label, i, cmd)
                else:
                    _emit_command(vc, b, lower, symbol_sorts, guard,
                                  block.label, cmd)

    _emit_cfg(vc, lower, program, guard, entry, cfg_encoding)

    pred = lower.lower_bool(ast.Var(assert_cond))
    vc.assert_failure_objective(vc.const("BLK_EXIT", Bool), guard(assert_block), pred)

    script = vc.script()
    return VcResult(
        script=script,
        smt_text=render_vc_script(script),
        assert_block=assert_block,
        asserts_before=asserts_before,
        merged=merged,
        gamma_sites=len(gamma_plan.sites),
    )


def _emit_gamma(vc, lower, program, sorts, plan, block_label, i, cmd) -> None:
    """A planned phi site: the total gamma `x = ite(K1, v1, ... phiRhs)`
    with the thin-gate case guards inlined, rendered from the same term
    mirror the annotator's anchors use (so the transpiled constraint
    matches the checker's rebuilt anchor verbatim)."""
    blocks = ttac_cfg.block_by_label(program)
    var_atom, cond_atom, guard_atom = encoder_atoms(program.entry, sanitize_name)
    name = cmd.target.name
    vc.const(name, lower.sort_of(name))
    rhs = tgamma_rhs_term(
        plan.sites[(block_label, i)],
        cmd.arms,
        plan.gates,
        blocks,
        is_int=sorts.get(name) == "int",
        var_atom=var_atom,
        cond_atom=cond_atom,
        guard_atom=guard_atom,
    )
    eq = ("eqI" if sorts.get(name) == "int" else "eqB", ("sym", name), rhs)
    vc.raw_fact(
        term_to_smt(eq),
        origin="gamma-def",
        comment=f"gamma merge for {name}",
    )


def _emit_command(vc, b, lower, sorts, guard, block_label, cmd) -> None:
    if isinstance(cmd, ast.Assert):
        return  # the single assert is the objective, emitted globally
    if isinstance(cmd, ast.Assign):
        name = cmd.target.name
        if sorts.get(name) == "bytemap":
            _emit_bytemap_assign(vc, lower, name, cmd.rhs, block_label)
        else:
            lhs = vc.const(name, lower.sort_of(name))
            b.def_(lhs, lower.lower_scalar(cmd.rhs))
    elif isinstance(cmd, ast.Havoc):
        name = cmd.target.name
        if sorts.get(name) == "bytemap":
            vc.bytemap.havoc(name)
        else:
            vc.const(name, lower.sort_of(name))  # declared, unconstrained
    elif isinstance(cmd, ast.Phi):
        name = cmd.target.name
        if sorts.get(name) == "bytemap":
            vc.bytemap.phi(
                name,
                [(guard(arm.label), lower.lower_map(ast.Var(arm.value))) for arm in cmd.arms],
            )
        else:
            cases = [
                (guard(arm.label), lower.lower_scalar(ast.Var(arm.value))) for arm in cmd.arms
            ]
            vc.dynamic_def(vc.const(name, lower.sort_of(name)), cases, guarded=False)
    elif isinstance(cmd, ast.Assume):
        b.assume(lower.lower_bool(cmd.cond))
    else:
        raise VcGenError(
            f"unsupported command {type(cmd).__name__} in block {block_label!r}; "
            "references must be desugared before vcgen"
        )


def _emit_bytemap_assign(vc, lower, name, rhs, block_label) -> None:
    if isinstance(rhs, ast.Update):
        vc.bytemap.store(
            name,
            lower.lower_map(rhs.base),
            lower.lower_int(rhs.index),
            lower.lower_scalar(rhs.value),
        )
    elif isinstance(rhs, ast.Var):
        src = lower.lower_map(rhs)
        vc.bytemap.define(name, lambda param, src=src: app(src.name, [param], Int))
    else:
        raise VcGenError(
            f"unsupported bytemap assignment in block {block_label!r}: "
            f"{type(rhs).__name__}"
        )


def _emit_cfg(vc, lower, program, guard, entry, cfg_encoding) -> None:
    encoder = CFG_ENCODERS.get(cfg_encoding)
    if encoder is None:
        avail = ", ".join(sorted(CFG_ENCODERS))
        raise VcGenError(f"unknown cfg encoding {cfg_encoding!r}; available: {avail}")

    labels = [b.label for b in program.blocks]
    idx = {label: i for i, label in enumerate(labels)}
    block_guards = tuple(guard(label).smt() for label in labels)

    edges: list[CfgEdge] = []
    for block in program.blocks:
        t = block.terminator
        if isinstance(t, ast.Goto):
            if t.target in idx:
                edges.append(CfgEdge(idx[block.label], idx[t.target], "true"))
        elif isinstance(t, ast.IfGoto):
            cond = lower.lower_bool(ast.Var(t.cond))
            if t.then_target in idx:
                edges.append(CfgEdge(idx[block.label], idx[t.then_target], cond.smt()))
            if t.else_target in idx:
                edges.append(CfgEdge(idx[block.label], idx[t.else_target], not_(cond).smt()))

    inp = CfgEncodeInput(
        block_ids=tuple(labels),
        block_guards=block_guards,
        entry=idx[entry],
        edges=tuple(edges),
    )
    vc.section("cfg constraints")
    encoder(
        inp,
        CfgEmit(
            add_constraint=lambda s: vc.raw_fact(s),
            add_decl=lambda n, srt: vc.const(n, Bool if srt == "Bool" else Int),
        ),
    )
