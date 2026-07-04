"""Tiny TAC -> Lean 4 transpiler (``ttac lean``).

Emits a self-contained lake project with two embeddings of the input
program: *deep* (a term of the hand-written ``Ttac`` inductive types in
``<repo>/lean/``, with a small-step semantics for proving properties of
VCGen) and *shallow* (per-block ``Prop`` definitions in native Lean, for
proving properties of the program itself).
"""

from .encode import LeanPrecheck, LeanResult, generate_lean, validate_for_lean
from .project import locate_ttac_lib, write_lean_project, write_vc_check_project
from .vccheck import VcCheckResult, generate_vc_check

__all__ = [
    "LeanPrecheck",
    "LeanResult",
    "VcCheckResult",
    "generate_lean",
    "generate_vc_check",
    "locate_ttac_lib",
    "validate_for_lean",
    "write_lean_project",
    "write_vc_check_project",
]
