"""Seahorn-style VC generation for TinyTAC.

Reuses the ctac VCGen library (``ctac.smt.vc``) and CFG-encoding library
(``ctac.smt.cfg``); only the expression mapping (:mod:`lower`) is
ttac-specific. References are out of scope (desugared beforehand).
"""

from __future__ import annotations

from .encode import VcResult, generate_vc
from .lower import TtacLowerer

__all__ = ["VcResult", "generate_vc", "TtacLowerer"]
