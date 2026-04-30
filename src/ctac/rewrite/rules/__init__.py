"""Rule library for the TAC rewriter.

Exported: :data:`default_pipeline` — the ordered tuple of rules used by
``ctac rw`` by default.
"""

from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.bitfield import (
    N1_SHIFTED_BWAND,
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
)
from ctac.rewrite.rules.bv_to_int import (
    ADD_BV_MAX_TO_ITE,
    ADD_BV_TO_INT,
    MUL_BV_TO_INT,
    SUB_BV_TO_INT,
)
from ctac.rewrite.rules.ceildiv import R6_CEILDIV
from ctac.rewrite.rules.bv_max_to_ite_validation import ADD_BV_MAX_TO_ITE_CASES
from ctac.rewrite.rules.ceildiv_validation import R6_CASES
from ctac.rewrite.rules.copyprop import CP_ALIAS
from ctac.rewrite.rules.cse import CSE
from ctac.rewrite.rules.div import (
    R1_BITFIELD_STRIP,
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
)
from ctac.rewrite.rules.div_purify import R4A_DIV_PURIFY
from ctac.rewrite.rules.div_purify_validation import R4A_CASES
from ctac.rewrite.rules.div_validation import R4_CASES
from ctac.rewrite.rules.div_validation_r1 import R1_CASES
from ctac.rewrite.validation import ValidationCase
from ctac.rewrite.rules.ite_purify import ITE_PURIFY
from ctac.rewrite.rules.purify_assert import PURIFY_ASSERT
from ctac.rewrite.rules.purify_assume import PURIFY_ASSUME
from ctac.rewrite.rules.range_fold import RANGE_FOLD
from ctac.rewrite.rules.store_eq import STORE_EQ_NORM, normalize_store_eq
from ctac.rewrite.rules.ite import (
    ADD_ITE_DIST,
    BOOL_ABSORB,
    DE_MORGAN,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    ITE_BOOL,
    ITE_COND_FOLD,
    ITE_SAME,
    SUB_ITE_DIST_LEFT,
    SUB_ITE_DIST_RIGHT,
)

# Phase 1 — chain recognition.
#
# Multi-command idioms (currently just R6's ceiling-division chain)
# need to be recognized BEFORE distribution rules can rewrite their
# constituent expressions. The rewrite driver does bottom-up
# traversal: at each iteration it visits subexpressions before parents.
# If a distribution rule (e.g. SUB_ITE_DIST_RIGHT) is in the same
# pipeline, it can fire on a sub-expression of the chain (rewriting
# `Sub(R_high, Ite(c, 1, 0))` into `Ite(c, Sub(R_high, 1), R_high)`)
# at a position deeper in the AST than where R6 would match — so by
# the time R6 looks at the chain's outer node, the chain has already
# been distorted past its recognizer's pattern.
#
# Splitting R6 + the bit-op canonicalizers it depends on into a
# dedicated phase guarantees they see the unmolested input.
chain_recognition_pipeline: tuple[Rule, ...] = (
    # Bit-op canonicalization: produce Mod / Div / Mul(Div(..), 2^k) so
    # downstream matchers see canonical forms.
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
    N1_SHIFTED_BWAND,
    # Multi-command chain recognizers. Run here, before any rule that
    # could rewrite chain interior expressions.
    R6_CEILDIV,
)


# Phase 2 — general simplification. Bit-op canonicalizers also live
# here so any chains that emerged in phase 1's output keep getting
# normalized within the fixed-point loop.
simplify_pipeline: tuple[Rule, ...] = (
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
    N1_SHIFTED_BWAND,
    # Existing const-divisor div rules + bitfield strip.
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
    R1_BITFIELD_STRIP,
    # Boolean / Ite simplification.
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    # Distribute Add/Sub over Ite operands so per-branch simplification
    # (constant folding, range-driven narrowing) can fire independently.
    ADD_ITE_DIST,
    SUB_ITE_DIST_LEFT,
    SUB_ITE_DIST_RIGHT,
    ITE_SAME,
    ITE_BOOL,
    # Range-driven Ite folding: decide `cond` via interval inference
    # and collapse to the then/else branch. Paired with ADD_BV_MAX_TO_ITE
    # below, which always emits an Ite; COND_FOLD collapses it when the
    # operand's range makes the condition decidable.
    ITE_COND_FOLD,
    BOOL_ABSORB,
    DE_MORGAN,
    # Range-safe narrowing: Mul/Add -> IntMul/IntAdd when interval
    # inference proves the result fits in [0, 2^256). Must run after the
    # div / bitfield rules so that the Mul(Div(..)) shapes they produce
    # become the canonical input here.
    MUL_BV_TO_INT,
    ADD_BV_TO_INT,
    SUB_BV_TO_INT,
    # Collapse expressions whose range is a singleton to the
    # corresponding ConstExpr. Runs after the narrowing rules so that
    # IntAdd / IntSub / ... produced above get folded to constants
    # when their ranges pin (e.g. Sub(X, Y) with equality assume).
    RANGE_FOLD,
    # Express Add(BV256_MAX, X) — the bv256 two's-complement decrement —
    # as an explicit Ite. ITE_COND_FOLD above collapses it whenever
    # range analysis decides `X >= 1`.
    ADD_BV_MAX_TO_ITE,
    # CP propagates aliases (Y := X). CSE deliberately runs in its own
    # phase (driven by the CLI), not here: CSE's RHS index is built once
    # per iteration, and rules that mutate registered RHSes (CP and the
    # simplifications above) shift canonical equivalence underneath the
    # snapshot. Isolating CSE makes the snapshot-correctness invariant
    # something we can actually rely on.
    CP_ALIAS,
)

# Stand-alone CSE phase. Runs CSE iteratively to fixed point with no
# other rule alongside it, so the per-iteration RHS index is stable
# (no other rule rewrites a registered RHS mid-iter and shifts canon
# equivalence). Driven by the CLI early (after chain recognition) and
# late (after ITE_PURIFY etc.) — see ``commands_rw.py``.
cse_pipeline: tuple[Rule, ...] = (CSE,)

# Full pipeline: chain recognition + simplification + purification. The
# CLI drives these as separate phases so chain recognizers see the
# unmolested input, distribution rules don't pre-empt R6, and R4a's
# Div-replacement happens last.
purify_pipeline: tuple[Rule, ...] = simplify_pipeline + (R4A_DIV_PURIFY,)

default_pipeline: tuple[Rule, ...] = purify_pipeline


# Validation cases collected from per-rule sibling files. Single source of
# truth for `ctac rw-valid`. Rules without an entry here have no soundness
# spec yet — the CLI reports them as "missing" so coverage gaps are visible.
validation_cases: tuple[ValidationCase, ...] = (
    R1_CASES + R4_CASES + R4A_CASES + R6_CASES + ADD_BV_MAX_TO_ITE_CASES
)

# Every rule name the rewriter exports, so `ctac rw-valid` can list the
# ones that don't yet have a spec.
all_rule_names: tuple[str, ...] = (
    N1_SHIFTED_BWAND.name,
    N2_LOW_MASK.name,
    N3_HIGH_MASK.name,
    N4_SHR_CONST.name,
    R1_BITFIELD_STRIP.name,
    R2_DIV_FUSE.name,
    R3_DIV_MUL_CANCEL.name,
    R4_DIV_IN_CMP.name,
    R4A_DIV_PURIFY.name,
    R6_CEILDIV.name,
    EQ_CONST_FOLD.name,
    EQ_ITE_DIST.name,
    ADD_ITE_DIST.name,
    SUB_ITE_DIST_LEFT.name,
    SUB_ITE_DIST_RIGHT.name,
    ITE_SAME.name,
    ITE_BOOL.name,
    ITE_COND_FOLD.name,
    BOOL_ABSORB.name,
    DE_MORGAN.name,
    MUL_BV_TO_INT.name,
    ADD_BV_TO_INT.name,
    SUB_BV_TO_INT.name,
    RANGE_FOLD.name,
    ADD_BV_MAX_TO_ITE.name,
    CSE.name,
    CP_ALIAS.name,
    ITE_PURIFY.name,
    PURIFY_ASSERT.name,
    PURIFY_ASSUME.name,
    STORE_EQ_NORM.name,
)

__all__ = [
    "ADD_BV_MAX_TO_ITE",
    "ADD_BV_TO_INT",
    "ADD_ITE_DIST",
    "BOOL_ABSORB",
    "CP_ALIAS",
    "CSE",
    "DE_MORGAN",
    "EQ_CONST_FOLD",
    "EQ_ITE_DIST",
    "ITE_BOOL",
    "ITE_COND_FOLD",
    "ITE_PURIFY",
    "ITE_SAME",
    "MUL_BV_TO_INT",
    "N1_SHIFTED_BWAND",
    "N2_LOW_MASK",
    "N3_HIGH_MASK",
    "N4_SHR_CONST",
    "PURIFY_ASSERT",
    "PURIFY_ASSUME",
    "R1_BITFIELD_STRIP",
    "R2_DIV_FUSE",
    "R3_DIV_MUL_CANCEL",
    "R4_DIV_IN_CMP",
    "R4A_DIV_PURIFY",
    "R6_CEILDIV",
    "RANGE_FOLD",
    "STORE_EQ_NORM",
    "SUB_BV_TO_INT",
    "SUB_ITE_DIST_LEFT",
    "SUB_ITE_DIST_RIGHT",
    "ValidationCase",
    "all_rule_names",
    "cse_pipeline",
    "default_pipeline",
    "normalize_store_eq",
    "purify_pipeline",
    "simplify_pipeline",
    "validation_cases",
]
