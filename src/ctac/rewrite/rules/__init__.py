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
from ctac.rewrite.rules.ceildiv import R6_CEILDIV
from ctac.rewrite.rules.copyprop import CP_ALIAS
from ctac.rewrite.rules.cse import CSE
from ctac.rewrite.rules.div import (
    R1_BITFIELD_STRIP,
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
)
from ctac.rewrite.rules.div_purify import R4A_DIV_PURIFY
from ctac.rewrite.rules.ite_purify import ITE_PURIFY
from ctac.rewrite.rules.ite import (
    BOOL_ABSORB,
    DE_MORGAN,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    ITE_BOOL,
    ITE_SAME,
)

# Rules that run *before* R4a (div purification). They handle bit-op
# canonicalization, the ceiling-div idiom, constant-divisor div simplification,
# and general boolean/Ite cleanup. Running R6 here (before R4a) ensures the
# ceiling chain collapses before R4a clobbers its inner IntDiv.
simplify_pipeline: tuple[Rule, ...] = (
    # Bit-op canonicalization: produce Mod / Div / Mul(Div(..), 2^k) so
    # downstream matchers see canonical forms.
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
    N1_SHIFTED_BWAND,
    # R6 before fine div rules so the ceiling-div chain collapses before
    # R3 / R4 pick at its pieces.
    R6_CEILDIV,
    # Existing const-divisor div rules + bitfield strip.
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
    R1_BITFIELD_STRIP,
    # Boolean / Ite simplification.
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    ITE_SAME,
    ITE_BOOL,
    BOOL_ABSORB,
    DE_MORGAN,
    # CSE before CP: fold duplicate static defs to aliases, then CP propagates
    # and DCE removes. Runs inside the fixed-point so CP's output can in turn
    # expose new CSE opportunities on the next iteration.
    CSE,
    CP_ALIAS,
)

# Full pipeline: simplification first, then purification. The CLI drives
# these as two phases so that R6 and the peephole div rules get their chance
# before R4a replaces any `Div` with a fresh symbol.
purify_pipeline: tuple[Rule, ...] = simplify_pipeline + (R4A_DIV_PURIFY,)

default_pipeline: tuple[Rule, ...] = purify_pipeline

__all__ = [
    "BOOL_ABSORB",
    "CP_ALIAS",
    "CSE",
    "DE_MORGAN",
    "EQ_CONST_FOLD",
    "EQ_ITE_DIST",
    "ITE_BOOL",
    "ITE_SAME",
    "N1_SHIFTED_BWAND",
    "N2_LOW_MASK",
    "N3_HIGH_MASK",
    "N4_SHR_CONST",
    "R1_BITFIELD_STRIP",
    "R2_DIV_FUSE",
    "R3_DIV_MUL_CANCEL",
    "ITE_PURIFY",
    "R4_DIV_IN_CMP",
    "R4A_DIV_PURIFY",
    "R6_CEILDIV",
    "default_pipeline",
    "purify_pipeline",
    "simplify_pipeline",
]
