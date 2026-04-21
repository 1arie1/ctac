"""Rule protocol + fixed-point driver for TAC rewrites.

Rules are expression-level functions: ``(expr, ctx) -> new_expr | None``. The
driver walks every :class:`AssignExpCmd` RHS and :class:`AssumeExpCmd`
condition bottom-up, applies rules at each subexpression, and rebuilds the
program. When any rule fires, the driver iterates again (up to
``max_iterations``) until a fixed point is reached.

Commands whose AST changes are canonicalized via :func:`canonicalize_cmd` so
their ``raw`` field stays consistent with the new expression tree.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass, field, replace

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.unparse import canonicalize_cmd

RuleFn = Callable[[TacExpr, RewriteCtx], "TacExpr | None"]


@dataclass(frozen=True)
class Rule:
    """A named, expression-level rewrite function."""

    name: str
    fn: RuleFn
    description: str = ""

    def apply(self, expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        return self.fn(expr, ctx)


@dataclass(frozen=True)
class RuleHit:
    rule: str
    block_id: str
    cmd_index: int
    iteration: int


@dataclass
class RewriteResult:
    program: TacProgram
    hits: tuple[RuleHit, ...] = field(default=())
    hits_by_rule: dict[str, int] = field(default_factory=dict)
    iterations: int = 0

    @property
    def total_hits(self) -> int:
        return len(self.hits)

    @property
    def changed(self) -> bool:
        return self.total_hits > 0


def _apply_rules_at(
    expr: TacExpr,
    rules: tuple[Rule, ...],
    ctx: RewriteCtx,
    hit_sink: list[str],
) -> TacExpr:
    """Try each rule at the top until none fires. Does not descend into children."""
    while True:
        fired = False
        for rule in rules:
            new_expr = rule.apply(expr, ctx)
            if new_expr is None:
                continue
            if new_expr is expr or new_expr == expr:
                continue
            hit_sink.append(rule.name)
            expr = new_expr
            fired = True
            break
        if not fired:
            return expr


def _rewrite_expr(
    expr: TacExpr,
    rules: tuple[Rule, ...],
    ctx: RewriteCtx,
    hit_sink: list[str],
) -> TacExpr:
    """Bottom-up: rewrite children, then try rules at the top."""
    if isinstance(expr, ApplyExpr):
        new_args: list[TacExpr] = []
        any_changed = False
        for arg in expr.args:
            new_arg = _rewrite_expr(arg, rules, ctx, hit_sink)
            new_args.append(new_arg)
            if new_arg is not arg:
                any_changed = True
        if any_changed:
            expr = replace(expr, args=tuple(new_args))
    return _apply_rules_at(expr, rules, ctx, hit_sink)


def rewrite_program(
    program: TacProgram,
    rules: tuple[Rule, ...] | list[Rule],
    *,
    max_iterations: int = 16,
    ite_max_depth: int = 4,
) -> RewriteResult:
    """Run ``rules`` over ``program`` to fixed point.

    Only RHS of :class:`AssignExpCmd` and condition of :class:`AssumeExpCmd` are
    considered. All other commands pass through unchanged.

    ``ite_max_depth`` caps how many nested Ite unions the range inferrer
    explores; beyond the cap it reports "unknown" and dependent rules bail.
    """
    rules_tuple: tuple[Rule, ...] = tuple(rules)
    all_hits: list[RuleHit] = []
    counts: Counter[str] = Counter()
    current = program
    iteration = 0

    while iteration < max_iterations:
        iteration += 1
        ctx = RewriteCtx(current, ite_max_depth=ite_max_depth)
        changed_this_iter = False
        new_blocks: list[TacBlock] = []
        for block in current.blocks:
            new_cmds: list[TacCmd] = []
            for idx, cmd in enumerate(block.commands):
                ctx.set_position(block.id, idx)
                cmd_hits: list[str] = []
                new_cmd: TacCmd = cmd
                if isinstance(cmd, AssignExpCmd):
                    new_rhs = _rewrite_expr(cmd.rhs, rules_tuple, ctx, cmd_hits)
                    if new_rhs is not cmd.rhs:
                        new_cmd = replace(cmd, rhs=new_rhs)
                elif isinstance(cmd, AssumeExpCmd):
                    new_cond = _rewrite_expr(cmd.condition, rules_tuple, ctx, cmd_hits)
                    if new_cond is not cmd.condition:
                        new_cmd = replace(cmd, condition=new_cond)
                if new_cmd is not cmd:
                    new_cmd = canonicalize_cmd(new_cmd)
                    changed_this_iter = True
                    for name in cmd_hits:
                        all_hits.append(
                            RuleHit(
                                rule=name,
                                block_id=block.id,
                                cmd_index=idx,
                                iteration=iteration,
                            )
                        )
                        counts[name] += 1
                new_cmds.append(new_cmd)
            new_blocks.append(replace(block, commands=new_cmds))
        current = TacProgram(blocks=new_blocks)
        if not changed_this_iter:
            break

    return RewriteResult(
        program=current,
        hits=tuple(all_hits),
        hits_by_rule=dict(counts),
        iterations=iteration,
    )
