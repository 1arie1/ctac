"""`ctac.cover` — sound decomposition procedures for single-assert TAC VCs.

Two strategies (independent decision procedures, not stacked):

- `ctac.cover.cfg`   — CFG cover (TAC-level path decomposition).
- `ctac.cover.alias` — alias cover (SMT-level aliasing decomposition).

Shared certification infrastructure (this round):

- `ctac.cover.subgoal`     — unclosed-subgoal data models.
- `ctac.cover.certificate` — SAT / UNSAT verdict certificates + `rerun.sh`.
- `ctac.cover.verify`      — independent re-verifier (`ctac verify-cover`).
"""
from __future__ import annotations

from ctac.cover.certificate import (
    Certificate,
    ClusterRecord,
    CompletenessProof,
    Decomposition,
    DecompositionKind,
    ProgramReplayPlan,
    SatCertificate,
    SubProof,
    UnsatCertificate,
    emit_sat_rerun_sh,
    emit_unsat_rerun_sh,
    load_certificate,
    save_certificate,
    write_rerun_sh,
)
from ctac.cover.subgoal import (
    ActionSuggestion,
    HardnessDiagnosis,
    HardnessLabel,
    SourceAnchor,
    Subgoal,
    SubgoalKind,
)

__all__ = [
    # subgoal
    'ActionSuggestion',
    'HardnessDiagnosis',
    'HardnessLabel',
    'SourceAnchor',
    'Subgoal',
    'SubgoalKind',
    # certificate
    'Certificate',
    'ClusterRecord',
    'CompletenessProof',
    'Decomposition',
    'DecompositionKind',
    'ProgramReplayPlan',
    'SatCertificate',
    'SubProof',
    'UnsatCertificate',
    'emit_sat_rerun_sh',
    'emit_unsat_rerun_sh',
    'load_certificate',
    'save_certificate',
    'write_rerun_sh',
]
