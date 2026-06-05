"""`ctac.cover` — sound decomposition procedures for single-assert TAC VCs.

One strategy today (alias cover, SMT-level aliasing decomposition, is future):

- `ctac.cover.cfg`   — CFG cover (TAC-level path decomposition).

Shared certification infrastructure (this round):

- `ctac.cover.subgoal`     — unclosed-subgoal data models.
- `ctac.cover.certificate` — SAT / UNSAT verdict certificates + `rerun.sh`.
- `ctac.cover.verify`      — independent re-verifier (`ctac verify-cover`).
"""
from __future__ import annotations

from ctac.cover.certificate import (
    Certificate,
    ClusterOutcome,
    ClusterRecord,
    CompletenessProof,
    CoverMetadata,
    Decomposition,
    DecompositionKind,
    PartialResult,
    ProbeOutcome,
    ProgramReplayPlan,
    SatCertificate,
    SubProof,
    UnsatCertificate,
    emit_partial_rerun_sh,
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
    'ClusterOutcome',
    'ClusterRecord',
    'CompletenessProof',
    'CoverMetadata',
    'Decomposition',
    'DecompositionKind',
    'PartialResult',
    'ProbeOutcome',
    'ProgramReplayPlan',
    'SatCertificate',
    'SubProof',
    'UnsatCertificate',
    'emit_partial_rerun_sh',
    'emit_sat_rerun_sh',
    'emit_unsat_rerun_sh',
    'load_certificate',
    'save_certificate',
    'write_rerun_sh',
]
