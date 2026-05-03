from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Protocol

from ctac.ir.models import TacFile
from ctac.smt.model import SmtScript
from ctac.smt.validate import AssertSite


class SmtEncodingError(ValueError):
    """Raised when an encoder cannot lower TAC into SMT-LIB."""


@dataclass(frozen=True)
class EncoderContext:
    tac_file: TacFile
    assert_site: AssertSite
    unsat_core: bool = False
    tight_logic: bool = False
    """If True, pick the tightest SMT-LIB logic the encoded VC fits into
    (e.g. ``QF_NIA`` when no uninterpreted functions are declared). When
    False (the default), encoders emit a broader logic by default
    (``QF_UFNIA`` for sea_vc) regardless of whether UF is actually used."""
    guard_statics: bool = False
    """If True, guard each static-def equality by its block-reachability
    variable: ``(=> BLK_<bid> (= lhs rhs))``. Default False emits the
    equality unconditionally as ``(= lhs rhs)`` regardless of which
    block the def lives in. Entry-block defs are unaffected either way
    (the entry guard is ``true``)."""
    guard_dynamics: bool = False
    """If True, encode each dynamic (DSA-merged) assignment as a
    block-guarded equality: ``(=> BLK_<bid> (= lhs rhs))`` per
    definition site. Default False merges the per-block defs into a
    single ``(= lhs (ite cond rhs ...))`` term selected by block
    guards. The guard form produces one assertion per defining block
    (deduped by RHS); the ITE form produces one assertion per symbol."""
    guard_axioms: bool = False
    """If True, guard each per-application UF axiom instantiation by
    the block-reachability variables of the blocks where the term
    that triggered the instantiation is encoded. Each axiom assert
    becomes ``(=> (or BLK_b1 BLK_b2 ...) <axiom_instance>)``; an
    axiom whose triggers all live in the entry block stays bare (the
    entry guard is ``true``). Covers the expensive per-application
    UF axioms (``bv256_xor_axiom``, ``int_ceil_div_axiom``,
    ``int_mul_div_axiom``). The bv256-range axioms on leaf bytemap
    UFs are deliberately *not* guarded — they are generic, cheap,
    and always sound to assert. Default False emits each UF axiom
    unconditionally. The guarded form is sound (the unguarded
    version dominates it); the win is in keeping the axiom out of
    the SMT core when its trigger block is not reachable on the
    current path."""
    cfg_encoding: str = "bwd0"
    """Which CFG-constraint encoding strategy to use. Five strategies
    ship today (``ctac.smt.cfg.CFG_ENCODERS``):
    ``bwd0`` (default) — predecessor-oriented edge-feasibility
      OR-of-ANDs + block-level existence + AMO. Historical sea_vc shape.
    ``bwd1`` — predecessor-oriented per-edge clausal implications,
      sound under the same AMO.
    ``fwd`` — successor-oriented one-way implication
      (``BLK_i => ⋁ BLK_succ``) + AMO over successors + per-edge guard.
    ``fwd-edge`` — like ``fwd`` but introduces per-edge Bool variables;
      block existence becomes a biconditional over edge vars
      (sound on diamond CFGs because edge vars decouple parents).
    ``bwd-edge`` — predecessor analog of ``fwd-edge``."""
    narrow_range: bool = False
    """If True, every static or dynamic ``AssignExpCmd`` whose RHS is a
    top-level ``Apply(safe_math_narrow_bvN:bif, ...)`` gets an extra
    range axiom on its LHS, derived from the LHS's declared bv-width.
    Currently only ``bv256`` LHS values are constrained (matching the
    havoc-range handler); other bv widths are silent. Default False
    preserves the historical encoding, which discards the narrow and
    leaves the LHS unconstrained beyond its sort."""
    store_reduce: bool = False
    """If True, build a per-bytemap chain data structure during encoding
    and use it to (1) prune shadowed Store entries when a later Store
    at the same key supersedes an earlier one, (2) preserve the
    ``(ite ... (M_old idx))`` shared-sibling form when no shadow fires,
    and (3) drop ``define-fun`` lines for bytemap symbols not
    reachable from any ``Select`` query (their content is inlined
    into the chain that reads them). Default False keeps the
    historical eager-emit shape unchanged. Sound by the array
    Store/Select axiom."""


class SmtEncoder(Protocol):
    name: str

    def encode(self, ctx: EncoderContext) -> SmtScript:
        ...


_EncoderFactory = Callable[[], SmtEncoder]
_ENCODERS: dict[str, _EncoderFactory] = {}


def register_encoder(name: str, factory: _EncoderFactory) -> None:
    key = name.strip().lower()
    if not key:
        raise ValueError("encoder name must be non-empty")
    _ENCODERS[key] = factory


def get_encoder(name: str) -> SmtEncoder:
    key = name.strip().lower()
    if key not in _ENCODERS:
        known = ", ".join(sorted(_ENCODERS))
        raise SmtEncodingError(f"unknown encoding {name!r}; available: {known}")
    return _ENCODERS[key]()


def available_encodings() -> tuple[str, ...]:
    return tuple(sorted(_ENCODERS))
