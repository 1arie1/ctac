"""TAC → TAC rewrite framework (expression-level peephole + tier-2 hook).

Public entry point: :func:`rewrite_program`. Rules live under :mod:`ctac.rewrite.rules`.
"""

from ctac.rewrite.framework import Rule, RewriteResult, RuleHit, rewrite_program
from ctac.rewrite.rules import default_pipeline
from ctac.rewrite.unparse import canonicalize_cmd, unparse_cmd, unparse_expr

__all__ = [
    "Rule",
    "RewriteResult",
    "RuleHit",
    "canonicalize_cmd",
    "default_pipeline",
    "rewrite_program",
    "unparse_cmd",
    "unparse_expr",
]
