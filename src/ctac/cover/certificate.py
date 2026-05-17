"""Cover verdict certificates: SAT witness + UNSAT decomposition.

A cover run that reaches a verdict emits ONE of:

- `SatCertificate`   — the original VC is SAT. Carries the slice z3
                       found SAT for, the z3 model, and a program
                       replay plan so `ctac run --validate` can
                       independently confirm the model triggers the
                       assert. No decomposition is needed: per the
                       first-SAT-wins rule, one witness suffices.

- `UnsatCertificate` — the original VC is UNSAT. Carries the cluster
                       decomposition, one `SubProof` per cluster
                       (all UNSAT), and a `CompletenessProof` showing
                       no CFG path escapes the union of cluster
                       keeps. Soundness composes: every execution
                       lies in some covered cluster, and every
                       covered cluster's VC is UNSAT.

Both certificates carry a `rerun_sh` — a bash script that
independently re-verifies the verdict. `ctac verify-cover` is the
typed re-verifier; the bash script is the read-by-humans audit
artifact and runs without ctac in the loop (just z3).

Soundness is a property of the certificate, NOT the search procedure
that produced it. If `rerun_sh` exits 0, the verdict is sound
regardless of any bugs in the cover loop.
"""
from __future__ import annotations

import json
import shlex
from dataclasses import dataclass
from pathlib import Path
from typing import Literal


SCHEMA_VERSION = 1

DecompositionKind = Literal['cfg-cluster', 'alpha-commit']


# ============================ Shared: ProgramReplayPlan ===========================


@dataclass(frozen=True)
class ProgramReplayPlan:
    """Plan for validating a SAT model against the original TAC.

    `ctac run` with `--model` and `--validate` loads the z3 model into
    the interpreter, runs the TAC concretely, and checks that the
    assert fires. This is the program-level confirmation that the
    abstract SAT lifts to the original semantics.

    `expected_outcome` is `'assert_fail'`: a SAT witness must reach
    an assert with a violating predicate. Anything else means the
    model doesn't actually witness SAT (e.g. trapped on an assume,
    silently coerced, or the model is for a different VC).
    """

    tac_path: str
    model_text_path: str
    ctac_run_args: tuple[str, ...] = ('--validate',)
    expected_outcome: Literal['assert_fail'] = 'assert_fail'

    def to_json_dict(self) -> dict:
        return {
            'tac_path': self.tac_path,
            'model_text_path': self.model_text_path,
            'ctac_run_args': list(self.ctac_run_args),
            'expected_outcome': self.expected_outcome,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> ProgramReplayPlan:
        return cls(
            tac_path=d['tac_path'],
            model_text_path=d['model_text_path'],
            ctac_run_args=tuple(d.get('ctac_run_args', ['--validate'])),
            expected_outcome=d.get('expected_outcome', 'assert_fail'),
        )


# ================================ SatCertificate =================================


@dataclass(frozen=True)
class SatCertificate:
    """A SAT verdict + everything needed to reproduce it.

    `witness_cluster` is the cluster id whose slice returned SAT (CFG
    cover) — informational, not load-bearing for soundness. `sat_smt2`
    is the actual file z3 found SAT for; verification re-solves THAT
    file and checks SAT. `program_replay` then lifts the z3 model
    back to the TAC.

    `witness_alpha` is reserved for alias cover (the α partition that
    yielded SAT); always None in v1.
    """

    sat_smt2: str
    z3_model: dict[str, str]            # name -> value (raw text)
    z3_invocation: tuple[str, ...]      # exact argv that produced SAT
    program_replay: ProgramReplayPlan
    rerun_sh: str                       # path to bash audit script
    witness_cluster: str | None = None  # cfg cover slice id
    witness_alpha: dict[str, str] | None = None   # alias cover α (future)
    wall_s: float = 0.0
    schema_version: int = SCHEMA_VERSION
    kind: Literal['sat'] = 'sat'

    def to_json_dict(self) -> dict:
        return {
            'schema_version': self.schema_version,
            'kind': self.kind,
            'witness_cluster': self.witness_cluster,
            'witness_alpha': (dict(self.witness_alpha)
                                if self.witness_alpha is not None else None),
            'sat_smt2': self.sat_smt2,
            'z3_model': dict(self.z3_model),
            'z3_invocation': list(self.z3_invocation),
            'wall_s': self.wall_s,
            'program_replay': self.program_replay.to_json_dict(),
            'rerun_sh': self.rerun_sh,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> SatCertificate:
        if d.get('kind') != 'sat':
            raise ValueError(f"expected kind='sat', got {d.get('kind')!r}")
        return cls(
            schema_version=int(d.get('schema_version', SCHEMA_VERSION)),
            witness_cluster=d.get('witness_cluster'),
            witness_alpha=(dict(d['witness_alpha'])
                             if d.get('witness_alpha') is not None else None),
            sat_smt2=d['sat_smt2'],
            z3_model={k: str(v) for k, v in d.get('z3_model', {}).items()},
            z3_invocation=tuple(d.get('z3_invocation', [])),
            wall_s=float(d.get('wall_s', 0.0)),
            program_replay=ProgramReplayPlan.from_json_dict(d['program_replay']),
            rerun_sh=d['rerun_sh'],
        )


# ================================ UnsatCertificate ===============================


@dataclass(frozen=True)
class ClusterRecord:
    """One cluster in a CFG cover decomposition.

    `keep_blocks` is the cluster's keep set (block IDs NOT dropped by
    pin); these define the cluster's wider sub-problem. `paths_covered`
    is informational — the count of sampled paths whose blocks lie
    entirely within `keep_blocks`."""

    id: str
    keep_blocks: tuple[str, ...]
    paths_covered: int = 0

    def to_json_dict(self) -> dict:
        return {
            'id': self.id,
            'keep_blocks': list(self.keep_blocks),
            'paths_covered': self.paths_covered,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> ClusterRecord:
        return cls(
            id=d['id'],
            keep_blocks=tuple(d.get('keep_blocks', [])),
            paths_covered=int(d.get('paths_covered', 0)),
        )


@dataclass(frozen=True)
class Decomposition:
    """The cover partition that the UNSAT certificate proves complete.

    For CFG cover (kind=`cfg-cluster`): `clusters` carries the cluster
    decomposition (cluster id + keep blocks). For alias cover
    (kind=`alpha-commit`): alpha partitions would live here; deferred
    to a future schema bump.
    """

    kind: DecompositionKind
    clusters: tuple[ClusterRecord, ...] = ()

    def to_json_dict(self) -> dict:
        return {
            'kind': self.kind,
            'clusters': [c.to_json_dict() for c in self.clusters],
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> Decomposition:
        return cls(
            kind=d['kind'],
            clusters=tuple(ClusterRecord.from_json_dict(c)
                            for c in d.get('clusters', [])),
        )


@dataclass(frozen=True)
class SubProof:
    """One cluster's UNSAT proof: SMT2 + the exact z3 invocation that
    produced UNSAT. `wall_s` is recorded for sanity (verify can warn
    when re-solve takes far longer than the original)."""

    sub_id: str
    smt2: str
    z3_invocation: tuple[str, ...]
    wall_s: float = 0.0
    expected_verdict: Literal['unsat'] = 'unsat'

    def to_json_dict(self) -> dict:
        return {
            'sub_id': self.sub_id,
            'smt2': self.smt2,
            'z3_invocation': list(self.z3_invocation),
            'wall_s': self.wall_s,
            'expected_verdict': self.expected_verdict,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> SubProof:
        return cls(
            sub_id=d['sub_id'],
            smt2=d['smt2'],
            z3_invocation=tuple(d.get('z3_invocation', [])),
            wall_s=float(d.get('wall_s', 0.0)),
            expected_verdict=d.get('expected_verdict', 'unsat'),
        )


@dataclass(frozen=True)
class CompletenessProof:
    """The CFG-completeness probe's UNSAT certificate.

    For CFG cover: the PB linear-path probe asks "does any feasible
    entry→assert CFG path escape every cluster's keep AND every prior
    unsat-core's block set?". UNSAT means no such path exists — every
    execution is covered. See `durable/auto-cover-strategy.md` for
    the full soundness argument.

    `semantic_argument` optionally points at a `soundness.md` narrative
    written by the cover run; verifying with the human-readable
    argument alongside the SMT verdict makes the proof auditable."""

    probe_smt2: str
    z3_invocation: tuple[str, ...]
    wall_s: float = 0.0
    expected_verdict: Literal['unsat'] = 'unsat'
    semantic_argument: str | None = None

    def to_json_dict(self) -> dict:
        return {
            'probe_smt2': self.probe_smt2,
            'z3_invocation': list(self.z3_invocation),
            'wall_s': self.wall_s,
            'expected_verdict': self.expected_verdict,
            'semantic_argument': self.semantic_argument,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> CompletenessProof:
        return cls(
            probe_smt2=d['probe_smt2'],
            z3_invocation=tuple(d.get('z3_invocation', [])),
            wall_s=float(d.get('wall_s', 0.0)),
            expected_verdict=d.get('expected_verdict', 'unsat'),
            semantic_argument=d.get('semantic_argument'),
        )


@dataclass(frozen=True)
class UnsatCertificate:
    """An UNSAT verdict + per-cluster proofs + completeness probe.

    Soundness composition: if every `sub_proofs[i]` re-solves to UNSAT
    AND `completeness_proof.probe_smt2` re-solves to UNSAT, then every
    feasible execution of the original program is covered by some
    cluster whose VC is UNSAT, so the original VC is UNSAT. The
    `rerun_sh` script encodes exactly this check."""

    decomposition: Decomposition
    sub_proofs: tuple[SubProof, ...]
    completeness_proof: CompletenessProof
    rerun_sh: str
    schema_version: int = SCHEMA_VERSION
    kind: Literal['unsat'] = 'unsat'

    def to_json_dict(self) -> dict:
        return {
            'schema_version': self.schema_version,
            'kind': self.kind,
            'decomposition': self.decomposition.to_json_dict(),
            'sub_proofs': [p.to_json_dict() for p in self.sub_proofs],
            'completeness_proof': self.completeness_proof.to_json_dict(),
            'rerun_sh': self.rerun_sh,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> UnsatCertificate:
        if d.get('kind') != 'unsat':
            raise ValueError(f"expected kind='unsat', got {d.get('kind')!r}")
        return cls(
            schema_version=int(d.get('schema_version', SCHEMA_VERSION)),
            decomposition=Decomposition.from_json_dict(d['decomposition']),
            sub_proofs=tuple(SubProof.from_json_dict(p)
                              for p in d.get('sub_proofs', [])),
            completeness_proof=CompletenessProof.from_json_dict(
                d['completeness_proof']),
            rerun_sh=d['rerun_sh'],
        )


# ================================ Certificate union ==============================


# Discriminated union — callers can dispatch on `cert.kind` ('sat' / 'unsat').
Certificate = SatCertificate | UnsatCertificate


def load_certificate(path: Path | str) -> Certificate:
    """Read a certificate JSON file and dispatch on `kind`."""
    p = Path(path)
    d = json.loads(p.read_text())
    k = d.get('kind')
    if k == 'sat':
        return SatCertificate.from_json_dict(d)
    if k == 'unsat':
        return UnsatCertificate.from_json_dict(d)
    raise ValueError(f"unknown certificate kind {k!r} in {p}")


def save_certificate(cert: Certificate, path: Path | str) -> None:
    """Write a certificate to JSON with stable formatting."""
    Path(path).write_text(
        json.dumps(cert.to_json_dict(), indent=2, sort_keys=True) + '\n')


# ================================ rerun.sh emitter ===============================


_RERUN_HEADER = """#!/usr/bin/env bash
# Auto-generated by `ctac cover-cfg` — independent verification script.
# Re-runs every sub-solve + completeness probe to confirm the cover
# verdict. Exits 0 on full match, non-zero on any deviation.
#
# Soundness: matching verdicts here ⇒ the cover verdict is sound,
# regardless of how the cover was produced.

set -euo pipefail
Z3="${Z3:-z3}"
FAIL=0

run_check() {
    # $1: label, $2: expected verdict, rest: z3 argv
    local label="$1"; shift
    local expected="$1"; shift
    echo "[check] $label ..."
    local got
    got=$("$@" 2>/dev/null | awk 'NR==1{print; exit}')
    if [[ "$got" == "$expected" ]]; then
        echo "[ ok ] $label = $got"
    else
        echo "[FAIL] $label expected=$expected got=$got"
        FAIL=1
    fi
}

"""


_RERUN_FOOTER = """
if [[ $FAIL -ne 0 ]]; then
    echo "VERIFY FAILED"
    exit 1
fi
echo "VERIFY OK"
"""


def _quote_argv(argv: tuple[str, ...] | list[str]) -> str:
    """Shell-quote each argument of an argv vector."""
    return ' '.join(shlex.quote(a) for a in argv)


def emit_sat_rerun_sh(cert: SatCertificate) -> str:
    """Render the bash audit script for a SAT certificate.

    Two checks:
    1. `z3 sat_smt2` returns sat (re-confirms the SAT verdict).
    2. `ctac run <tac> --model <model.txt> --validate` triggers
       `assert_fail=1` (lifts the model to program semantics).

    The model file is referenced by `program_replay.model_text_path`
    — the caller is expected to have written it before running this
    script."""
    z3_args = _quote_argv(cert.z3_invocation) if cert.z3_invocation \
        else f'"$Z3" -smt2 {shlex.quote(cert.sat_smt2)}'
    replay = cert.program_replay
    replay_argv = ['ctac', 'run', replay.tac_path,
                    '--model', replay.model_text_path]
    replay_argv += list(replay.ctac_run_args)
    return (
        _RERUN_HEADER
        + f'run_check "z3 SAT confirm" sat {z3_args}\n'
        + f'echo "[check] program replay: {replay.tac_path}"\n'
        + f'if {_quote_argv(replay_argv)} 2>&1 | '
            'grep -q "^assert_fail.*: 1"; then\n'
        + '    echo "[ ok ] replay: assert_fail = 1"\n'
        + 'else\n'
        + '    echo "[FAIL] replay did not produce assert_fail=1"\n'
        + '    FAIL=1\n'
        + 'fi\n'
        + _RERUN_FOOTER
    )


def emit_unsat_rerun_sh(cert: UnsatCertificate) -> str:
    """Render the bash audit script for an UNSAT certificate.

    For each `SubProof`: re-solve and assert verdict == 'unsat'.
    Then: re-solve the completeness probe and assert UNSAT.

    All sub-proofs and the probe must pass; any single deviation
    exits non-zero. The cover verdict is sound iff this script
    exits 0."""
    parts = [_RERUN_HEADER]
    for sp in cert.sub_proofs:
        argv = (_quote_argv(sp.z3_invocation) if sp.z3_invocation
                  else f'"$Z3" -smt2 {shlex.quote(sp.smt2)}')
        parts.append(f'run_check "sub {sp.sub_id}" unsat {argv}\n')
    probe = cert.completeness_proof
    probe_argv = (_quote_argv(probe.z3_invocation) if probe.z3_invocation
                    else f'"$Z3" -smt2 {shlex.quote(probe.probe_smt2)}')
    parts.append(f'run_check "completeness probe" unsat {probe_argv}\n')
    parts.append(_RERUN_FOOTER)
    return ''.join(parts)


def write_rerun_sh(cert: Certificate, path: Path | str) -> None:
    """Write the rerun.sh for a certificate and mark it executable."""
    p = Path(path)
    if cert.kind == 'sat':
        text = emit_sat_rerun_sh(cert)
    else:
        text = emit_unsat_rerun_sh(cert)
    p.write_text(text)
    p.chmod(0o755)
