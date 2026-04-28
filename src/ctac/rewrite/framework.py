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
    AssertCmd,
    AssignExpCmd,
    AssumeExpCmd,
    JumpCmd,
    JumpiCmd,
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
    extra_symbols: tuple[tuple[str, str], ...] = field(default=())
    warnings: tuple[str, ...] = field(default=())

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
    *,
    at_top: bool,
) -> TacExpr:
    """Try each rule at the top until none fires. Does not descend into children."""
    while True:
        fired = False
        # ctx.at_cmd_top() reflects whether this call site is the outermost
        # expression of the host cmd — used by rules that want to replace the
        # whole command (R4a/R6 reuse the host LHS as the havoc name).
        ctx._at_cmd_top = at_top
        for rule in rules:
            new_expr = rule.apply(expr, ctx)
            if new_expr is None:
                continue
            if new_expr is expr or new_expr == expr:
                continue
            hit_sink.append(rule.name)
            expr = new_expr
            fired = True
            # After a rule fires, the expression we hold is fresh — ensure the
            # next attempt re-evaluates at the same "top" position.
            ctx._at_cmd_top = at_top
            break
        if not fired:
            return expr


def _rewrite_expr(
    expr: TacExpr,
    rules: tuple[Rule, ...],
    ctx: RewriteCtx,
    hit_sink: list[str],
    *,
    at_top: bool = True,
) -> TacExpr:
    """Bottom-up: rewrite children, then try rules at the top.

    ``at_top`` marks the outermost call (the expression passed by the driver
    for an :class:`AssignExpCmd` RHS or :class:`AssumeExpCmd` condition).
    Recursive calls into children pass ``at_top=False``.
    """
    if isinstance(expr, ApplyExpr):
        new_args: list[TacExpr] = []
        any_changed = False
        for arg in expr.args:
            new_arg = _rewrite_expr(arg, rules, ctx, hit_sink, at_top=False)
            new_args.append(new_arg)
            if new_arg is not arg:
                any_changed = True
        if any_changed:
            expr = replace(expr, args=tuple(new_args))
    return _apply_rules_at(expr, rules, ctx, hit_sink, at_top=at_top)


def _splice_into_entry_block(
    program: TacProgram, new_cmds: list[TacCmd]
) -> TacProgram:
    """Insert ``new_cmds`` into the entry block, just before its terminator.

    If the entry block has no terminator, appends at the end. Each inserted
    command passes through :func:`canonicalize_cmd` so ``raw`` is populated.
    """
    if not program.blocks or not new_cmds:
        return program
    entry = program.blocks[0]
    prepared = [canonicalize_cmd(c) for c in new_cmds]
    term_idx = next(
        (i for i, c in enumerate(entry.commands) if isinstance(c, (JumpCmd, JumpiCmd))),
        len(entry.commands),
    )
    merged = list(entry.commands[:term_idx]) + prepared + list(entry.commands[term_idx:])
    new_entry = replace(entry, commands=merged)
    return TacProgram(blocks=[new_entry, *program.blocks[1:]])


def _apply_per_position_edits(
    program: TacProgram,
    insertions: dict[tuple[str, int], list[TacCmd]],
    skips: set[tuple[str, int]],
) -> TacProgram:
    """Insert before-positions and drop skip-positions in a single pass.

    Both the insertion dict and the skip set reference pre-edit indices;
    combining them into one walk avoids the index-shift pitfall that would
    arise from applying them separately.
    """
    if not insertions and not skips:
        return program
    inserts_by_block: dict[str, dict[int, list[TacCmd]]] = {}
    for (bid, idx), cmds in insertions.items():
        inserts_by_block.setdefault(bid, {})[idx] = [canonicalize_cmd(c) for c in cmds]
    skips_by_block: dict[str, set[int]] = {}
    for bid, idx in skips:
        skips_by_block.setdefault(bid, set()).add(idx)
    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        ins = inserts_by_block.get(block.id)
        drop = skips_by_block.get(block.id)
        if not ins and not drop:
            new_blocks.append(block)
            continue
        cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            if ins and idx in ins:
                cmds.extend(ins[idx])
            if drop and idx in drop:
                continue
            cmds.append(cmd)
        new_blocks.append(replace(block, commands=cmds))
    return TacProgram(blocks=new_blocks)


def rewrite_program(
    program: TacProgram,
    rules: tuple[Rule, ...] | list[Rule],
    *,
    max_iterations: int = 16,
    ite_max_depth: int = 4,
    symbol_sorts: dict[str, str] | None = None,
    use_int_ceil_div: bool = True,
) -> RewriteResult:
    """Run ``rules`` over ``program`` to fixed point.

    Only RHS of :class:`AssignExpCmd` and condition of :class:`AssumeExpCmd` are
    considered for expression rewrites. Rules may additionally request
    fresh havoc-and-assume pairs via :meth:`RewriteCtx.emit_fresh_var`; those
    are spliced into the entry block at the end of each outer iteration.

    ``ite_max_depth`` caps how many nested Ite unions the range inferrer
    explores; beyond the cap it reports "unknown" and dependent rules bail.

    ``symbol_sorts`` maps declared symbol names to sorts (``"bv256"``,
    ``"int"``, ``"bool"``). Optional; rules that rely on sort-based bounds
    (e.g. defaulting a bv256 symbol's range to ``[0, 2^256 - 1]``) fall back
    to dominating assume-facts only when it's empty.

    ``use_int_ceil_div`` toggles R6's emit shape between the new
    ``IntCeilDiv``-as-concept form (default) and the legacy ``havoc +
    polynomial-bounds`` form. The latter remains the performance-validated
    benchmark; the former is gated to let us explore SMT interaction.
    """
    rules_tuple: tuple[Rule, ...] = tuple(rules)
    all_hits: list[RuleHit] = []
    counts: Counter[str] = Counter()
    current = program
    iteration = 0
    extra_symbols: list[tuple[str, str]] = []
    fresh_counter = 0

    while iteration < max_iterations:
        iteration += 1
        ctx = RewriteCtx(
            current,
            ite_max_depth=ite_max_depth,
            fresh_counter_start=fresh_counter,
            symbol_sorts=symbol_sorts or {},
            use_int_ceil_div=use_int_ceil_div,
        )
        changed_this_iter = False
        new_blocks: list[TacBlock] = []
        # We need the skip-set available while assembling per-block output, so
        # snapshot it now (rules may add to it during this iteration's walk).
        for block in current.blocks:
            new_cmds: list[TacCmd] = []
            for idx, cmd in enumerate(block.commands):
                ctx.set_position(block.id, idx)
                cmd_hits: list[str] = []
                new_cmd: TacCmd = cmd
                if isinstance(cmd, AssignExpCmd):
                    ctx.set_host_cmd(cmd, at_top=True)
                    new_rhs = _rewrite_expr(cmd.rhs, rules_tuple, ctx, cmd_hits)
                    if new_rhs is not cmd.rhs:
                        new_cmd = replace(cmd, rhs=new_rhs)
                elif isinstance(cmd, AssumeExpCmd):
                    ctx.set_host_cmd(cmd, at_top=True)
                    new_cond = _rewrite_expr(cmd.condition, rules_tuple, ctx, cmd_hits)
                    if new_cond is not cmd.condition:
                        new_cmd = replace(cmd, condition=new_cond)
                elif isinstance(cmd, AssertCmd):
                    ctx.set_host_cmd(cmd, at_top=True)
                    new_pred = _rewrite_expr(cmd.predicate, rules_tuple, ctx, cmd_hits)
                    if new_pred is not cmd.predicate:
                        new_cmd = replace(cmd, predicate=new_pred)
                else:
                    ctx.set_host_cmd(None, at_top=False)
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

        entry_pending, pos_pending, pending_syms, pending_skips, fresh_counter = (
            ctx.drain_pending()
        )
        if entry_pending:
            current = _splice_into_entry_block(current, entry_pending)
            changed_this_iter = True
        if pos_pending or pending_skips:
            current = _apply_per_position_edits(current, pos_pending, pending_skips)
            changed_this_iter = True
        if pending_syms:
            extra_symbols.extend(pending_syms)

        if not changed_this_iter:
            break

    return RewriteResult(
        program=current,
        hits=tuple(all_hits),
        hits_by_rule=dict(counts),
        iterations=iteration,
        extra_symbols=tuple(extra_symbols),
        warnings=tuple(ctx.warnings),
    )
