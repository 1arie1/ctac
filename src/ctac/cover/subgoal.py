"""Cover subgoal artifact: an unclosed sub-problem with provenance.

A *subgoal* is a structurally-simple-but-hard SMT2 (and optionally TAC)
emitted by a cover run as a residual — the cover identified the
sub-problem but couldn't close it in its budget. Each subgoal carries:

- the artifact files (smt2 + optional tac/rw_tac);
- source anchors mapping it back to the original program;
- a hardness diagnosis from the z3 runner;
- ready-to-run action suggestions for the user / downstream tools.

Two kinds, reflecting the cover-architecture asymmetry
(`durable/auto-cover-strategy.md` + `cover-architecture.md`):

- ``cfg-cluster``: emitted by CFG cover. Has TAC + rw_tac + smt2.
- ``alpha-commit``: emitted by alias cover. SMT2 only — alias
  commitments don't survive a TAC re-emission, so a TAC view of an
  alpha-commit subgoal doesn't exist.

Subgoals are pure data; they serialize to/from JSON and are referenced
from the cover manifest. They are NOT involved in the soundness
argument — that lives in `ctac.cover.certificate`. Subgoals are how
the cover communicates "here is what I couldn't close, and what you
might do about it".
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal


SCHEMA_VERSION = 1

SubgoalKind = Literal['cfg-cluster', 'alpha-commit']

# Recognized hardness classes. The taxonomy is extensible; ``unknown``
# is the residual bucket whose contents inform future labels.
HardnessLabel = Literal[
    'nlsat-bottleneck',
    'lp-bp-aliasing-memory',
    'bytemap-uf-blowup',
    'boolean-sat-only',
    'unknown',
]


# -------------------------------- SourceAnchor --------------------------------


@dataclass(frozen=True)
class SourceAnchor:
    """Mapping from a subgoal back to a region of the original program.

    Populated from TAC ``meta`` annotations that survive SMT emission
    (function name, file, line range) and/or from SBF metadata. Fields
    are independently optional — partial information is still useful.
    """

    function: str | None = None
    file: str | None = None
    line_start: int | None = None
    line_end: int | None = None
    sbf_address_range: tuple[int, int] | None = None  # inclusive (lo, hi)

    def to_json_dict(self) -> dict:
        return {
            'function': self.function,
            'file': self.file,
            'line_start': self.line_start,
            'line_end': self.line_end,
            'sbf_address_range': (list(self.sbf_address_range)
                                    if self.sbf_address_range is not None
                                    else None),
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> SourceAnchor:
        sar = d.get('sbf_address_range')
        return cls(
            function=d.get('function'),
            file=d.get('file'),
            line_start=d.get('line_start'),
            line_end=d.get('line_end'),
            sbf_address_range=(tuple(sar) if sar is not None else None),  # type: ignore[arg-type]
        )


# ------------------------------ HardnessDiagnosis -----------------------------


@dataclass(frozen=True)
class HardnessDiagnosis:
    """Classifier output for a stuck subgoal.

    Populated by `ctac.cover.cfg.classify` (which wraps
    `ctac.solver.DiagnosticSignature` from the z3 runner). For alias
    cover residuals, the classifier sees only the abstract solve's
    stats — fine for label/confidence but not for rationale specifics.
    """

    label: HardnessLabel
    confidence: float  # 0..1
    signature: dict[str, float] = field(default_factory=dict)  # the stats
    rationale: str = ''

    def to_json_dict(self) -> dict:
        return {
            'label': self.label,
            'confidence': self.confidence,
            'signature': dict(self.signature),
            'rationale': self.rationale,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> HardnessDiagnosis:
        return cls(
            label=d['label'],
            confidence=float(d.get('confidence', 0.0)),
            signature={k: float(v) for k, v in d.get('signature', {}).items()},
            rationale=d.get('rationale', ''),
        )


# ------------------------------ ActionSuggestion -----------------------------


@dataclass(frozen=True)
class ActionSuggestion:
    """A ready-to-run next step for a stuck subgoal.

    `command` is verbatim shell text the user can paste. `label` and
    `expected_payoff` are human-readable rationale shown in
    ``report.md``."""

    label: str
    command: str
    expected_payoff: str = ''

    def to_json_dict(self) -> dict:
        return {
            'label': self.label,
            'command': self.command,
            'expected_payoff': self.expected_payoff,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> ActionSuggestion:
        return cls(
            label=d['label'],
            command=d['command'],
            expected_payoff=d.get('expected_payoff', ''),
        )


# ----------------------------------- Subgoal ---------------------------------


@dataclass(frozen=True)
class Subgoal:
    """An unclosed sub-problem emitted by a cover run.

    Paths are stored as strings (POSIX-ish). The convention is "relative
    to the manifest's directory when possible, absolute otherwise" —
    callers serializing should normalize before constructing.

    `parent_vc` is the original input the cover started from (`.tac` for
    CFG cover, `.smt2` for alias cover). `rerun_cmd` is a ready-to-run
    shell line that re-solves THIS subgoal in isolation — useful for
    `ctac verify-cover` and for users picking a residual to attack."""

    id: str
    kind: SubgoalKind
    smt2: str
    parent_vc: str
    rerun_cmd: str

    tac: str | None = None                   # cfg-cluster only
    rw_tac: str | None = None                # cfg-cluster only (post rw)
    source_anchors: tuple[SourceAnchor, ...] = ()
    hardness: HardnessDiagnosis | None = None
    suggested_actions: tuple[ActionSuggestion, ...] = ()
    schema_version: int = SCHEMA_VERSION

    def to_json_dict(self) -> dict:
        return {
            'schema_version': self.schema_version,
            'id': self.id,
            'kind': self.kind,
            'smt2': self.smt2,
            'tac': self.tac,
            'rw_tac': self.rw_tac,
            'parent_vc': self.parent_vc,
            'source_anchors': [a.to_json_dict() for a in self.source_anchors],
            'hardness': (self.hardness.to_json_dict()
                          if self.hardness is not None else None),
            'suggested_actions': [a.to_json_dict()
                                    for a in self.suggested_actions],
            'rerun_cmd': self.rerun_cmd,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> Subgoal:
        h = d.get('hardness')
        return cls(
            schema_version=int(d.get('schema_version', SCHEMA_VERSION)),
            id=d['id'],
            kind=d['kind'],
            smt2=d['smt2'],
            tac=d.get('tac'),
            rw_tac=d.get('rw_tac'),
            parent_vc=d['parent_vc'],
            source_anchors=tuple(
                SourceAnchor.from_json_dict(a)
                for a in d.get('source_anchors', [])),
            hardness=(HardnessDiagnosis.from_json_dict(h)
                       if h is not None else None),
            suggested_actions=tuple(
                ActionSuggestion.from_json_dict(a)
                for a in d.get('suggested_actions', [])),
            rerun_cmd=d['rerun_cmd'],
        )
