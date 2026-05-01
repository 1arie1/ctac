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
