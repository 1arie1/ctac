from __future__ import annotations

import dataclasses

from ctac.ir.models import TacFile
from ctac.smt.encoding import (
    EncoderContext,
    SmtEncodingError,
    available_encodings,
    get_encoder,
    register_encoder,
)
from ctac.smt.encoding.sea_vc import SeaVcEncoder
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
from ctac.splitcrit import split_critical_edges

register_encoder("sea_vc", SeaVcEncoder)


_BV_ADD_SUB_AXIOM_VARIANTS = ("no-mod", "mod")


def build_vc(
    tac_file: TacFile,
    *,
    encoding: str = "sea_vc",
    unsat_core: bool = False,
    tight_logic: bool = False,
    guard_statics: bool = False,
    guard_dynamics: bool = False,
    guard_axioms: bool = False,
    cfg_encoding: str = "bwd0",
    narrow_range: bool = False,
    bv_add_sub_axiom: str = "no-mod",
    store_reduce: bool = False,
    inline_scalars: bool = False,
) -> SmtScript:
    if bv_add_sub_axiom not in _BV_ADD_SUB_AXIOM_VARIANTS:
        known = ", ".join(_BV_ADD_SUB_AXIOM_VARIANTS)
        raise SmtEncodingError(
            f"unknown bv_add_sub_axiom {bv_add_sub_axiom!r}; available: {known}"
        )
    # Pre-pass: break any critical edges so sea_vc's predecessor
    # exclusivity stays sound. Idempotent when the input is already clean.
    split = split_critical_edges(tac_file.program)
    tac_file = dataclasses.replace(tac_file, program=split.program)
    assert_site = validate_program_for_smt(tac_file.program)
    encoder = get_encoder(encoding)
    return encoder.encode(
        EncoderContext(
            tac_file=tac_file,
            assert_site=assert_site,
            unsat_core=unsat_core,
            tight_logic=tight_logic,
            guard_statics=guard_statics,
            guard_dynamics=guard_dynamics,
            guard_axioms=guard_axioms,
            cfg_encoding=cfg_encoding,
            narrow_range=narrow_range,
            bv_add_sub_axiom=bv_add_sub_axiom,
            store_reduce=store_reduce,
            inline_scalars=inline_scalars,
        )
    )


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
