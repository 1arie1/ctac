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


SCHEMA_VERSION = 2

DecompositionKind = Literal['cfg-cluster', 'alpha-commit']


# =============================== CoverMetadata ===================================


@dataclass(frozen=True)
class CoverMetadata:
    """Reproducibility metadata baked into every certificate.

    The audit chain (`rerun.sh` + `ctac verify-cover`) re-derives each
    cluster's smt2 from `input_tac` using `rw_flags` / `smt_flags`,
    then re-solves with `z3_bin`. `z3_version` is informational: the
    verifier warns on mismatch but doesn't fail (since z3 versions
    can be compatible across the verdict)."""

    input_tac: str                              # path to original TAC
    z3_bin: str                                 # path to the z3 binary used
    z3_version: str                             # output of `z3 --version`
    rw_flags: tuple[str, ...] = ()
    smt_flags: tuple[str, ...] = ()
    ctac_version: str = ''                      # informational; verify-cover ignores

    def to_json_dict(self) -> dict:
        return {
            'input_tac': self.input_tac,
            'z3_bin': self.z3_bin,
            'z3_version': self.z3_version,
            'rw_flags': list(self.rw_flags),
            'smt_flags': list(self.smt_flags),
            'ctac_version': self.ctac_version,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> CoverMetadata:
        return cls(
            input_tac=d['input_tac'],
            z3_bin=d.get('z3_bin', 'z3'),
            z3_version=d.get('z3_version', ''),
            rw_flags=tuple(d.get('rw_flags', [])),
            smt_flags=tuple(d.get('smt_flags', [])),
            ctac_version=d.get('ctac_version', ''),
        )


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

    metadata: CoverMetadata             # NEW v2: input_tac, z3 ver, flags
    sat_smt2: str
    winner_drops: tuple[str, ...]       # NEW v2: drops for the SAT cluster
    z3_model: dict[str, str]            # name -> value (raw text)
    z3_args: tuple[str, ...]            # NEW v2: persistent args (no -T, no -smt2)
    program_replay: ProgramReplayPlan   # NB: tac_path → INPUT_TAC, not slice
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
            'metadata': self.metadata.to_json_dict(),
            'witness_cluster': self.witness_cluster,
            'witness_alpha': (dict(self.witness_alpha)
                                if self.witness_alpha is not None else None),
            'sat_smt2': self.sat_smt2,
            'winner_drops': list(self.winner_drops),
            'z3_model': dict(self.z3_model),
            'z3_args': list(self.z3_args),
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
            metadata=CoverMetadata.from_json_dict(d['metadata']),
            witness_cluster=d.get('witness_cluster'),
            witness_alpha=(dict(d['witness_alpha'])
                             if d.get('witness_alpha') is not None else None),
            sat_smt2=d['sat_smt2'],
            winner_drops=tuple(d.get('winner_drops', [])),
            z3_model={k: str(v) for k, v in d.get('z3_model', {}).items()},
            z3_args=tuple(d.get('z3_args', [])),
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
    """One cluster's UNSAT proof.

    Audit chain (see `CoverMetadata`):
    1. `ctac pin INPUT_TAC --drop <drops> -o pinned.tac`
    2. `ctac rw pinned.tac <rw_flags> -o pinned.rw.tac`
    3. `ctac smt pinned.rw.tac <smt_flags> -o v.smt2`
    4. `z3 -T:VERIFY_TIMEOUT -smt2 v.smt2 <z3_args>` → expect `unsat`

    `drops` are the blocks dropped from INPUT_TAC to materialize this
    cluster. `z3_args` is the persistent z3 invocation (no `-T`, no
    `-smt2 <file>`); the verifier supplies its own timeout. `wall_s`
    is informational (verify can warn on >>original)."""

    sub_id: str
    smt2: str
    drops: tuple[str, ...]                    # NEW v2: for re-derivation
    z3_args: tuple[str, ...] = ()             # NEW v2: replaces z3_invocation
    wall_s: float = 0.0
    expected_verdict: Literal['unsat'] = 'unsat'

    def to_json_dict(self) -> dict:
        return {
            'sub_id': self.sub_id,
            'smt2': self.smt2,
            'drops': list(self.drops),
            'z3_args': list(self.z3_args),
            'wall_s': self.wall_s,
            'expected_verdict': self.expected_verdict,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> SubProof:
        return cls(
            sub_id=d['sub_id'],
            smt2=d['smt2'],
            drops=tuple(d.get('drops', [])),
            z3_args=tuple(d.get('z3_args', [])),
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
    z3_args: tuple[str, ...] = ()             # NEW v2 (no -T, no -smt2 <file>)
    wall_s: float = 0.0
    expected_verdict: Literal['unsat'] = 'unsat'
    semantic_argument: str | None = None

    def to_json_dict(self) -> dict:
        return {
            'probe_smt2': self.probe_smt2,
            'z3_args': list(self.z3_args),
            'wall_s': self.wall_s,
            'expected_verdict': self.expected_verdict,
            'semantic_argument': self.semantic_argument,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> CompletenessProof:
        return cls(
            probe_smt2=d['probe_smt2'],
            z3_args=tuple(d.get('z3_args', [])),
            wall_s=float(d.get('wall_s', 0.0)),
            expected_verdict=d.get('expected_verdict', 'unsat'),
            semantic_argument=d.get('semantic_argument'),
        )


@dataclass(frozen=True)
class ClusterOutcome:
    """Per-cluster outcome for the partial manifest.

    Carries the full picture (whether the cluster closed or not), so
    the manifest can distinguish what needs more work. `verdict` is
    one of `sat` / `unsat` / `timeout` / `unknown` / `error`."""

    sub_id: str
    smt2: str
    drops: tuple[str, ...]
    verdict: str
    z3_args: tuple[str, ...] = ()
    wall_s: float = 0.0

    def to_json_dict(self) -> dict:
        return {
            'sub_id': self.sub_id,
            'smt2': self.smt2,
            'drops': list(self.drops),
            'verdict': self.verdict,
            'z3_args': list(self.z3_args),
            'wall_s': self.wall_s,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> ClusterOutcome:
        return cls(
            sub_id=d['sub_id'],
            smt2=d['smt2'],
            drops=tuple(d.get('drops', [])),
            verdict=d['verdict'],
            z3_args=tuple(d.get('z3_args', [])),
            wall_s=float(d.get('wall_s', 0.0)),
        )


@dataclass(frozen=True)
class ProbeOutcome:
    """Completeness-probe verdict for the partial manifest. `verdict`
    is one of `sat` / `unsat` / `timeout` / `unknown`."""

    probe_smt2: str
    verdict: str
    z3_args: tuple[str, ...] = ()
    wall_s: float = 0.0

    def to_json_dict(self) -> dict:
        return {
            'probe_smt2': self.probe_smt2,
            'verdict': self.verdict,
            'z3_args': list(self.z3_args),
            'wall_s': self.wall_s,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> ProbeOutcome:
        return cls(
            probe_smt2=d['probe_smt2'],
            verdict=d['verdict'],
            z3_args=tuple(d.get('z3_args', [])),
            wall_s=float(d.get('wall_s', 0.0)),
        )


@dataclass(frozen=True)
class PartialResult:
    """Cover ran but didn't reach a sound sat/unsat verdict.

    This is NOT a certificate — it doesn't justify a verdict. It IS
    a structured diagnostic: per-cluster outcomes + (optionally) the
    completeness probe's verdict, so a user can see exactly what
    needs more work.

    The two key questions a user asks of a partial result:
    - "Do my clusters need more compute?" → see `clusters_need_closure`.
    - "Or is the cover itself incomplete (missing paths)?" →
      see `cover_is_incomplete`.

    If `clusters_need_closure and not cover_is_incomplete`:
        Closing the open clusters is sufficient.
    If `cover_is_incomplete`:
        Closing open clusters alone is NOT sufficient — some CFG path
        escapes every cluster's keep. Sample more paths.

    `closed_sub_proofs` are valid UNSAT SubProofs from the closed
    clusters — re-verifiable in the same way as UnsatCertificate's
    sub-proofs. The partial verifier re-runs these alongside reporting
    the open ones."""

    metadata: CoverMetadata
    verdict: Literal['timeout', 'unknown']
    cluster_outcomes: tuple[ClusterOutcome, ...]
    closed_sub_proofs: tuple[SubProof, ...]
    probe_outcome: ProbeOutcome | None = None
    rerun_sh: str = 'rerun.sh'
    schema_version: int = SCHEMA_VERSION
    kind: Literal['partial'] = 'partial'

    @property
    def clusters_need_closure(self) -> bool:
        return any(c.verdict not in ('sat', 'unsat')
                     for c in self.cluster_outcomes)

    @property
    def probe_needs_closure(self) -> bool:
        return (self.probe_outcome is None
                or self.probe_outcome.verdict != 'unsat')

    @property
    def cover_is_incomplete(self) -> bool:
        """Probe explicitly SAT means some CFG path escapes every
        cluster's keep — closing open clusters is NOT enough."""
        return (self.probe_outcome is not None
                and self.probe_outcome.verdict == 'sat')

    def to_json_dict(self) -> dict:
        return {
            'schema_version': self.schema_version,
            'kind': self.kind,
            'verdict': self.verdict,
            'metadata': self.metadata.to_json_dict(),
            'cluster_outcomes': [c.to_json_dict()
                                   for c in self.cluster_outcomes],
            'closed_sub_proofs': [p.to_json_dict()
                                    for p in self.closed_sub_proofs],
            'probe_outcome': (self.probe_outcome.to_json_dict()
                                if self.probe_outcome is not None else None),
            'rerun_sh': self.rerun_sh,
            # Computed booleans surfaced as data for cli/audit tooling:
            'clusters_need_closure': self.clusters_need_closure,
            'probe_needs_closure': self.probe_needs_closure,
            'cover_is_incomplete': self.cover_is_incomplete,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> PartialResult:
        if d.get('kind') != 'partial':
            raise ValueError(
                f"expected kind='partial', got {d.get('kind')!r}")
        probe = d.get('probe_outcome')
        return cls(
            schema_version=int(d.get('schema_version', SCHEMA_VERSION)),
            verdict=d['verdict'],
            metadata=CoverMetadata.from_json_dict(d['metadata']),
            cluster_outcomes=tuple(
                ClusterOutcome.from_json_dict(c)
                for c in d.get('cluster_outcomes', [])),
            closed_sub_proofs=tuple(
                SubProof.from_json_dict(p)
                for p in d.get('closed_sub_proofs', [])),
            probe_outcome=(ProbeOutcome.from_json_dict(probe)
                             if probe is not None else None),
            rerun_sh=d.get('rerun_sh', 'rerun.sh'),
        )


@dataclass(frozen=True)
class UnsatCertificate:
    """An UNSAT verdict + per-cluster proofs + completeness probe.

    Soundness composition: if every `sub_proofs[i]` re-solves to UNSAT
    AND `completeness_proof.probe_smt2` re-solves to UNSAT, then every
    feasible execution of the original program is covered by some
    cluster whose VC is UNSAT, so the original VC is UNSAT. The
    `rerun_sh` script encodes exactly this check."""

    metadata: CoverMetadata             # NEW v2
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
            'metadata': self.metadata.to_json_dict(),
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
            metadata=CoverMetadata.from_json_dict(d['metadata']),
            decomposition=Decomposition.from_json_dict(d['decomposition']),
            sub_proofs=tuple(SubProof.from_json_dict(p)
                              for p in d.get('sub_proofs', [])),
            completeness_proof=CompletenessProof.from_json_dict(
                d['completeness_proof']),
            rerun_sh=d['rerun_sh'],
        )


# ================================ Certificate union ==============================


# Discriminated union — callers can dispatch on `.kind`. Sat/Unsat
# are *sound* certificates; Partial is a structured diagnostic for
# incomplete cover runs (no soundness claim).
Certificate = SatCertificate | UnsatCertificate | PartialResult


def load_certificate(path: Path | str) -> Certificate:
    """Read a manifest JSON file and dispatch on `kind`."""
    p = Path(path)
    d = json.loads(p.read_text())
    k = d.get('kind')
    if k == 'sat':
        return SatCertificate.from_json_dict(d)
    if k == 'unsat':
        return UnsatCertificate.from_json_dict(d)
    if k == 'partial':
        return PartialResult.from_json_dict(d)
    raise ValueError(f"unknown certificate kind {k!r} in {p}")


def save_certificate(cert: Certificate, path: Path | str) -> None:
    """Write a certificate to JSON with stable formatting."""
    Path(path).write_text(
        json.dumps(cert.to_json_dict(), indent=2, sort_keys=True) + '\n')


# ================================ rerun.sh emitter ===============================


_RERUN_PROLOGUE_TEMPLATE = """#!/usr/bin/env bash
# Auto-generated by `ctac cover-cfg` — independent verification script.
# Re-derives every cluster's smt2 from INPUT_TAC (via ctac pin / rw /
# smt) before re-solving with z3. Catches bugs anywhere in the pin /
# rw / smt / z3 chain. Exit 0 on full match, non-zero on any deviation.
#
# Soundness: matching verdicts here ⇒ the cover verdict is sound,
# regardless of how the cover was produced.
#
# Per-z3-step timeout is derived from the cover's recorded wall_s:
#   budget = max(wall_s * VERIFY_TIMEOUT_MULTIPLIER + VERIFY_TIMEOUT_SLACK, 10)
# If the audit needs much more than the recording, that's a signal —
# either a bug, environmental drift, or a non-reproducible cover.
#
# Env overrides:
#   CTAC=<path>                       ctac binary (default: ctac on PATH)
#   Z3=<path>                         z3 binary (default: recorded path)
#   VERIFY_TIMEOUT_MULTIPLIER=<n>     z3 budget multiplier (default 2)
#   VERIFY_TIMEOUT_SLACK=<sec>        z3 budget slack (default 5)

set -eu
CTAC="${{CTAC:-ctac}}"
Z3="${{Z3:-{recorded_z3_bin}}}"
VERIFY_TIMEOUT_MULTIPLIER="${{VERIFY_TIMEOUT_MULTIPLIER:-2}}"
VERIFY_TIMEOUT_SLACK="${{VERIFY_TIMEOUT_SLACK:-5}}"
FAIL=0
INPUT_TAC={input_tac_q}
EXPECTED_Z3_VERSION={z3_version_q}

# Compute per-z3 budget from recorded wall_s.
z3_budget() {{
    # $1: recorded wall seconds (may have decimals)
    local recorded="$1"
    awk -v r="$recorded" \\
        -v m="$VERIFY_TIMEOUT_MULTIPLIER" \\
        -v s="$VERIFY_TIMEOUT_SLACK" \\
        'BEGIN {{
            t = r * m + s + 0.999
            if (t < 10) t = 10
            printf "%d", t
        }}'
}}

# Resolve to absolute path; the script changes into the audit dir below
# so the recorded relative paths resolve consistently.
INPUT_TAC=$(cd "$(dirname "$INPUT_TAC")" 2>/dev/null && pwd)/$(basename "$INPUT_TAC") \\
    || INPUT_TAC="$INPUT_TAC"

# Audit dir = the directory this script lives in (so the script is
# location-independent: copy the cover/ tree anywhere and run rerun.sh).
AUDIT_DIR=$(cd "$(dirname "${{BASH_SOURCE[0]}}")" && pwd)
cd "$AUDIT_DIR"

# Warn (don't fail) on z3 version mismatch.
got_version=$("$Z3" --version 2>&1 | head -n 1 || echo '<no z3>')
if [[ "$got_version" != "$EXPECTED_Z3_VERSION" ]]; then
    echo "[warn] z3 version mismatch: expected '$EXPECTED_Z3_VERSION', got '$got_version'"
fi

run_step() {{
    # $1: label, rest: argv. Fails loudly on non-zero rc.
    local label="$1"; shift
    if ! "$@" > "${{label}}.log" 2>&1; then
        echo "[FAIL] step '$label' returned non-zero; see ${{label}}.log"
        FAIL=1
        return 1
    fi
}}

check_verdict() {{
    # $1: label, $2: expected verdict, rest: z3 argv
    local label="$1"; shift
    local expected="$1"; shift
    echo "[check] $label ..."
    local out
    out=$("$@" 2>&1 || true)
    local got
    got=$(printf '%s\\n' "$out" | head -n 1 | tr -d '[:space:]')
    if [[ "$got" == "$expected" ]]; then
        echo "[ ok ] $label = $got"
    else
        echo "[FAIL] $label expected=$expected got=$got"
        FAIL=1
    fi
}}

rederive_cluster() {{
    # $1: cluster dir, $2: drops (comma-separated; may be empty)
    #
    # Pin / rw / smt are bounded TAC transforms; no z3 hanging risk.
    # We don't wrap them in a portable shell `timeout` (not present
    # on stock macOS). On unexpected hang, the user Ctrl-C's.
    local dir="$1"; local drops="$2"
    mkdir -p "$dir"
    local drop_args=()
    if [[ -n "$drops" ]]; then
        drop_args=(--drop "$drops")
    fi
    "$CTAC" pin "$INPUT_TAC" -o "$dir/pinned.tac" --plain "${{drop_args[@]}}" \\
        > "${{dir}}.pin.log" 2>&1 || \\
        {{ echo "[FAIL] pin $dir; see ${{dir}}.pin.log"; FAIL=1; return 1; }}
    "$CTAC" rw "$dir/pinned.tac" -o "$dir/pinned.rw.tac" --plain {rw_flags_q} \\
        > "${{dir}}.rw.log" 2>&1 || \\
        {{ echo "[FAIL] rw $dir; see ${{dir}}.rw.log"; FAIL=1; return 1; }}
    "$CTAC" smt "$dir/pinned.rw.tac" -o "$dir/v.smt2" --plain {smt_flags_q} \\
        > "${{dir}}.smt.log" 2>&1 || \\
        {{ echo "[FAIL] smt $dir; see ${{dir}}.smt.log"; FAIL=1; return 1; }}
}}

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


def _prologue(meta: CoverMetadata) -> str:
    """Render the shared bash prologue with metadata baked in."""
    return _RERUN_PROLOGUE_TEMPLATE.format(
        input_tac_q=shlex.quote(meta.input_tac),
        recorded_z3_bin=shlex.quote(meta.z3_bin),
        z3_version_q=shlex.quote(meta.z3_version),
        rw_flags_q=_quote_argv(meta.rw_flags),
        smt_flags_q=_quote_argv(meta.smt_flags),
    )


def emit_sat_rerun_sh(cert: SatCertificate) -> str:
    """Render the bash audit script for a SAT certificate.

    Steps:
    1. Re-derive the winner cluster's smt2 from INPUT_TAC
       (`pin --drop <winner_drops>` → `rw` → `smt`).
    2. Solve the re-derived smt2; expect `sat`.
    3. Capture z3's model.
    4. Replay against **INPUT_TAC** (not the slice): `ctac run
       INPUT_TAC --model <model> --validate` triggers `assert_fail`.

    Replay targets INPUT_TAC because the cover's soundness claim is
    "the original program is SAT" — the slice's model must drive the
    original assert."""
    winner_id = cert.witness_cluster or 'winner'
    drops_s = ','.join(cert.winner_drops)
    z3_args = _quote_argv(cert.z3_args)
    parts: list[str] = [_prologue(cert.metadata)]
    parts.append(f'rederive_cluster {shlex.quote(winner_id)} '
                  f'{shlex.quote(drops_s)}\n')
    parts.append(f'T=$(z3_budget {cert.wall_s:.3f})\n')
    parts.append(
        f'echo "[budget] sat-confirm: recorded {cert.wall_s:.2f}s, '
        f'budget ${{T}}s"\n')
    parts.append(
        f'check_verdict "z3 SAT confirm" sat '
        f'"$Z3" -T:"$T" -smt2 '
        f'{shlex.quote(winner_id + "/v.smt2")} {z3_args}\n')
    # Capture the model.
    parts.append(
        f'echo "[step] capturing z3 model"\n'
        f'"$Z3" -T:"$T" -smt2 {shlex.quote(winner_id + "/v.smt2")} '
        f'{z3_args} -model > {shlex.quote(winner_id + "/model.smt")}\n')
    # Replay against INPUT_TAC.
    replay = cert.program_replay
    extra = _quote_argv(replay.ctac_run_args)
    parts.append(
        f'echo "[check] program replay: INPUT_TAC"\n'
        f'if "$CTAC" run "$INPUT_TAC" --model '
        f'{shlex.quote(winner_id + "/model.smt")} {extra} --plain 2>&1 '
        f'| grep -q "^assert_fail.*: [1-9]"; then\n'
        f'    echo "[ ok ] replay: assert_fail >= 1"\n'
        f'else\n'
        f'    echo "[FAIL] replay did not produce assert_fail >= 1"\n'
        f'    FAIL=1\n'
        f'fi\n')
    parts.append(_RERUN_FOOTER)
    return ''.join(parts)


def emit_unsat_rerun_sh(cert: UnsatCertificate) -> str:
    """Render the bash audit script for an UNSAT certificate.

    For each `SubProof`: re-derive pin/rw/smt from INPUT_TAC + solve;
    expect `unsat`. Then re-solve the completeness probe (stored
    smt2; the probe emitter is pure Python so re-emit would not catch
    its own bugs)."""
    parts = [_prologue(cert.metadata)]
    for sp in cert.sub_proofs:
        sub_dir = Path(sp.smt2).parent.as_posix()  # e.g. "cluster_0"
        drops_s = ','.join(sp.drops)
        z3_args_s = _quote_argv(sp.z3_args)
        parts.append(
            f'rederive_cluster {shlex.quote(sub_dir)} '
            f'{shlex.quote(drops_s)}\n')
        parts.append(f'T=$(z3_budget {sp.wall_s:.3f})\n')
        parts.append(
            f'echo "[budget] {sp.sub_id}: recorded {sp.wall_s:.2f}s, '
            f'budget ${{T}}s"\n')
        parts.append(
            f'check_verdict "sub {sp.sub_id}" unsat '
            f'"$Z3" -T:"$T" -smt2 {shlex.quote(sp.smt2)} '
            f'{z3_args_s}\n')
    probe = cert.completeness_proof
    probe_args_s = _quote_argv(probe.z3_args)
    parts.append(f'T=$(z3_budget {probe.wall_s:.3f})\n')
    parts.append(
        f'echo "[budget] completeness probe: recorded {probe.wall_s:.2f}s, '
        f'budget ${{T}}s"\n')
    parts.append(
        f'check_verdict "completeness probe" unsat '
        f'"$Z3" -T:"$T" -smt2 {shlex.quote(probe.probe_smt2)} '
        f'{probe_args_s}\n')
    parts.append(_RERUN_FOOTER)
    return ''.join(parts)


def emit_partial_rerun_sh(cert: PartialResult) -> str:
    """Render the bash audit script for a partial result.

    Re-derives and re-solves every CLOSED cluster (sub-proofs);
    re-solves the probe if it ran. Exit code is always non-zero —
    partial isn't a sound verdict — but the script reports exactly
    what closed vs. what didn't."""
    parts = [_prologue(cert.metadata)]
    parts.append(f'# Partial result: overall verdict = '
                  f'{cert.verdict}\n')
    parts.append(f'# clusters_need_closure = {cert.clusters_need_closure}\n')
    parts.append(f'# probe_needs_closure   = {cert.probe_needs_closure}\n')
    parts.append(f'# cover_is_incomplete   = {cert.cover_is_incomplete}\n\n')
    # Re-verify the closed sub-proofs.
    for sp in cert.closed_sub_proofs:
        sub_dir = Path(sp.smt2).parent.as_posix()
        drops_s = ','.join(sp.drops)
        z3_args_s = _quote_argv(sp.z3_args)
        parts.append(
            f'rederive_cluster {shlex.quote(sub_dir)} '
            f'{shlex.quote(drops_s)}\n')
        parts.append(f'T=$(z3_budget {sp.wall_s:.3f})\n')
        parts.append(
            f'echo "[budget] {sp.sub_id}: recorded {sp.wall_s:.2f}s, '
            f'budget ${{T}}s"\n')
        parts.append(
            f'check_verdict "sub {sp.sub_id}" unsat '
            f'"$Z3" -T:"$T" -smt2 {shlex.quote(sp.smt2)} '
            f'{z3_args_s}\n')
    # Probe (if it ran).
    if cert.probe_outcome is not None:
        probe = cert.probe_outcome
        probe_args_s = _quote_argv(probe.z3_args)
        parts.append(f'T=$(z3_budget {probe.wall_s:.3f})\n')
        parts.append(
            f'echo "[budget] probe: recorded {probe.wall_s:.2f}s, '
            f'budget ${{T}}s; recorded verdict={probe.verdict}"\n')
        parts.append(
            f'check_verdict "completeness probe" '
            f'{probe.verdict} '
            f'"$Z3" -T:"$T" -smt2 {shlex.quote(probe.probe_smt2)} '
            f'{probe_args_s}\n')
    # Open clusters: report only.
    open_outcomes = [c for c in cert.cluster_outcomes
                       if c.verdict not in ('sat', 'unsat')]
    for c in open_outcomes:
        parts.append(
            f'echo "[open] {c.sub_id} (verdict={c.verdict}, '
            f'recorded {c.wall_s:.2f}s) — needs more compute or analysis"\n')
    parts.append('\n# Partial results never pass `VERIFY OK` — overall '
                  'verdict is\n# {cert.verdict}; mark the script as failed.\n'
                  .format(cert=cert))
    parts.append('FAIL=1\n')
    parts.append(_RERUN_FOOTER)
    return ''.join(parts)


def write_rerun_sh(cert: Certificate, path: Path | str) -> None:
    """Write the rerun.sh for a certificate and mark it executable."""
    p = Path(path)
    if cert.kind == 'sat':
        text = emit_sat_rerun_sh(cert)
    elif cert.kind == 'unsat':
        text = emit_unsat_rerun_sh(cert)
    else:
        text = emit_partial_rerun_sh(cert)
    p.write_text(text)
    p.chmod(0o755)
