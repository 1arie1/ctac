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
