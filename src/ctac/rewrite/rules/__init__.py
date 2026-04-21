"""Rule library for the TAC rewriter.

Exported: :data:`default_pipeline` — the ordered tuple of rules used by
``ctac rw`` by default.
"""

from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.bitfield import N1_SHIFTED_BWAND
from ctac.rewrite.rules.copyprop import CP_ALIAS
from ctac.rewrite.rules.div import (
    R1_BITFIELD_STRIP,
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
)
from ctac.rewrite.rules.ite import (
    BOOL_ABSORB,
    DE_MORGAN,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    ITE_BOOL,
    ITE_SAME,
)

default_pipeline: tuple[Rule, ...] = (
    N1_SHIFTED_BWAND,
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
    R1_BITFIELD_STRIP,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    ITE_SAME,
    ITE_BOOL,
    BOOL_ABSORB,
    DE_MORGAN,
    CP_ALIAS,
)

__all__ = [
    "BOOL_ABSORB",
    "CP_ALIAS",
    "DE_MORGAN",
    "EQ_CONST_FOLD",
    "EQ_ITE_DIST",
    "ITE_BOOL",
    "ITE_SAME",
    "N1_SHIFTED_BWAND",
    "R1_BITFIELD_STRIP",
    "R2_DIV_FUSE",
    "R3_DIV_MUL_CANCEL",
    "R4_DIV_IN_CMP",
    "default_pipeline",
]
