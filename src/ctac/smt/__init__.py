from __future__ import annotations

from ctac.ir.models import TacFile
from ctac.smt.encoding import (
    EncoderContext,
    SmtEncodingError,
    available_encodings,
    get_encoder,
    register_encoder,
)
from ctac.smt.encoding.sea_vc import SeaVcEncoder
from ctac.smt.encoding.vc_path_predicates import VCPathPredicatesEncoder
from ctac.smt.model import SmtDeclaration, SmtScript
from ctac.smt.render import render_smt_script
from ctac.smt.validate import (
    AssertSite,
    SmtValidationError,
    ensure_acyclic,
    ensure_assert_last,
    find_assert_site,
    validate_program_for_smt,
)

register_encoder("vc-path-predicates", VCPathPredicatesEncoder)
register_encoder("sea_vc", SeaVcEncoder)


def build_vc(tac_file: TacFile, *, encoding: str = "vc-path-predicates") -> SmtScript:
    assert_site = validate_program_for_smt(tac_file.program)
    encoder = get_encoder(encoding)
    return encoder.encode(EncoderContext(tac_file=tac_file, assert_site=assert_site))


__all__ = [
    "AssertSite",
    "SmtDeclaration",
    "SmtEncodingError",
    "SmtScript",
    "SmtValidationError",
    "available_encodings",
    "build_vc",
    "ensure_acyclic",
    "ensure_assert_last",
    "find_assert_site",
    "get_encoder",
    "register_encoder",
    "render_smt_script",
    "validate_program_for_smt",
]
