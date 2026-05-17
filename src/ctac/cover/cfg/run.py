"""CFG cover orchestrator — the CEGAR loop that ties everything together.

The cover's job (per `durable/auto-cover-strategy.md`'s 2026-05-15
reframe): **prove UNSAT for the original VC, or yield ONE SAT
witness**. First-SAT-wins; the completeness loop only runs after
every cluster fails to find SAT.

Outline:

1. Load + sample + cluster.
2. Materialize each cluster (`pin --drop` complement + rw + smt).
3. Parallel solve clusters with `accept = (verdict == 'sat')`.
   First SAT → write `SatCertificate` and return.
4. All clusters non-SAT → completeness loop:
     For iter in 1..MAX_ITER:
       - Emit probe(cluster_keeps, forbidden_paths).
       - z3 the probe (small budget).
       - UNSAT → UnsatCertificate; return.
       - SAT → derive escape path π.
         a. *Absorb*: try widening a near-by cluster (small budget).
            On absorbed UNSAT → update K_j, continue.
            On absorbed SAT  → SatCertificate; return.
         b. *Singleton + core*: materialize π as a singleton cluster
            with --unsat-core; solve.
            On SAT  → SatCertificate; return.
            On UNSAT → parse core; add core-blocks as forbid clause.
            On unknown → forbid the full π's block set.
5. Max-iter reached without UNSAT → report residual subgoals and
   return verdict='unknown'.

The output directory layout matches `durable/auto-cover-strategy.md`:

  <out_dir>/
    manifest.json          # the Certificate (SAT or UNSAT)
    rerun.sh               # bash audit script
    report.md              # human-readable summary
    cluster_<i>/           # per-cluster artifacts
    completeness/          # probe smt2 per iter
    subgoals/              # residuals (if any)
"""
from __future__ import annotations

import shutil
import subprocess
import time
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from ctac.cover.certificate import (
    ClusterOutcome,
    ClusterRecord,
    CompletenessProof,
    CoverMetadata,
    Decomposition,
    PartialResult,
    ProbeOutcome,
    ProgramReplayPlan,
    SatCertificate,
    SubProof,
    UnsatCertificate,
    save_certificate,
    write_rerun_sh,
)
from ctac.cover.cfg.absorb import try_absorb
from ctac.cover.cfg.cfg_graph import blocks_on_entry_to_assert_paths, load_cfg
from ctac.cover.cfg.classify import classify, suggest_actions
from ctac.cover.cfg.cluster import Cluster, auto_k, cluster_paths
from ctac.cover.cfg.completeness import derive_path_from_model, emit_probe
from ctac.cover.cfg.core_blocks import core_blocks_from_stdout
from ctac.cover.cfg.materialize import (
    DEFAULT_RW_FLAGS,
    DEFAULT_SMT_FLAGS,
    ClusterArtifacts,
    MaterializeError,
    materialize_cluster,
)
from ctac.cover.cfg.sampling import sample_paths, saturate_paths
from ctac.cover.subgoal import Subgoal
from ctac.ir.models import NBId
from ctac.solver.config import Z3Config
from ctac.solver.race import RaceResult, RaceTask, race
from ctac.solver.runner import Z3RunResult
from ctac.solver.z3 import resolve_z3_bin, solve as solver_solve


# -------------------------------- Config -------------------------------------


@dataclass(frozen=True)
class CoverConfig:
    """Knobs for the cover loop. Defaults match the prototype's
    validated settings (`durable/auto-cover-strategy.md`)."""

    samples: int = 32
    k: int | None = None                 # None → auto_k(samples)
    cluster_budget_s: int = 30
    absorb_budget_s: int = 8
    absorb_threshold: int = 5
    completeness_iter: int = 30
    completeness_budget_s: int = 30
    workers: int = 4
    seed: int = 0
    saturate_max_added: int = 64


# ----------------------------- Results / state -------------------------------


@dataclass
class ClusterState:
    """Per-cluster tracking during the loop."""

    cluster: Cluster
    artifacts: ClusterArtifacts
    verdict: str | None = None
    wall_s: float = 0.0
    z3_argv: tuple[str, ...] = ()
    signature_label: str | None = None
    signature: dict | None = None


@dataclass
class CoverResult:
    verdict: Literal['sat', 'unsat', 'timeout', 'unknown']
    manifest_path: Path
    report_path: Path
    rerun_sh_path: Path
    wall_s: float
    n_clusters: int
    n_completeness_iters: int
    subgoals: list[Subgoal] = field(default_factory=list)


# ----------------------------- Solve helpers ---------------------------------


def _accept_sat(r: Z3RunResult) -> bool:
    """Race accept: first SAT verdict wins (kills the rest)."""
    return r.verdict == 'sat'


def _accept_sat_or_open(r: Z3RunResult) -> bool:
    """Race accept under `--abort-on-timeout`: SAT wins, OR any
    timeout / unknown / error aborts the race (those are signals
    that the cover can't reach a sound UNSAT anyway, so don't burn
    cycles on remaining clusters)."""
    return r.verdict in ('sat', 'timeout', 'unknown', 'error')


def _solve_clusters_parallel(states: list[ClusterState], *,
                                budget_s: int,
                                workers: int,
                                z3_bin: Path,
                                cluster_z3_args: Sequence[str] = (),
                                abort_on_timeout: bool = False,
                                ) -> RaceResult:
    """Parallel race over cluster VCs. First SAT wins; remainder
    SIGKILL'd. If no SAT verdict, all clusters run to completion.

    `cluster_z3_args` is the user-supplied z3 pass-through (seeds,
    tactics, ...). Applied to every cluster solve uniformly.

    `abort_on_timeout=True` makes any non-`unsat` non-`sat` verdict
    abort the race — useful when you want to stop sampling at the
    first sign of trouble."""
    args = tuple(cluster_z3_args)
    tasks = [
        RaceTask(config=Z3Config(name=st.cluster.id, args=args),
                  seed=0, smt2=Path(st.artifacts.smt2),
                  timeout_s=budget_s, z3_bin=z3_bin)
        for st in states
    ]
    label_to_state = {t.label: st for t, st in zip(tasks, states)}

    accept = _accept_sat_or_open if abort_on_timeout else _accept_sat
    result = race(tasks, max_concurrent=workers, accept=accept)
    # Fold results back into states.
    for task, run_result in result.all_results:
        st = label_to_state.get(task.label)
        if st is None:
            continue
        st.verdict = run_result.verdict
        st.wall_s = run_result.wall_s
        st.z3_argv = tuple(run_result.argv)
        if run_result.signature is not None:
            st.signature_label = run_result.signature.label
            st.signature = {k: v for k, v in run_result.signature.signals.items()
                              if isinstance(v, (int, float))}
    return result


def _solve_one(smt2: Path, *, budget_s: int,
                z3_bin: Path,
                extra_args: Sequence[str] = (),
                ) -> tuple[str, float, list[str], str, str]:
    """One-shot z3 invocation via `ctac.solver.z3.solve()`. Returns
    (verdict, wall_s, argv, stdout, stderr). Used by completeness
    probe, absorption, and singleton+core paths."""
    res = solver_solve(smt2, timeout_s=budget_s, z3_bin=z3_bin,
                        extra_args=extra_args)
    return res.verdict, res.wall_s, res.argv, res.stdout, res.stderr


def _persistent_args(argv: list[str] | tuple[str, ...],
                       smt2_path: str | Path) -> tuple[str, ...]:
    """Strip the binary, `-T:N`, `-smt2 <file>`, and observation flags
    (`-v:N`) from a recorded argv. Returns the persistent args — those
    the audit verifier needs to reproduce the verdict (seeds, tactics,
    `-st`, anything else) while supplying its own timeout."""
    smt2_s = str(smt2_path)
    out: list[str] = []
    skip_next = False
    for a in argv[1:]:  # skip argv[0] (binary path)
        if skip_next:
            skip_next = False
            continue
        if a.startswith('-T:'):
            continue
        if a.startswith('-v:'):
            continue
        if a == '-smt2':
            skip_next = True
            continue
        if a == smt2_s:
            continue
        out.append(a)
    return tuple(out)


def _z3_version(z3_bin: Path) -> str:
    """Capture `z3 --version` for the certificate metadata."""
    try:
        proc = subprocess.run([str(z3_bin), '--version'],
                                capture_output=True, text=True, timeout=10)
        return proc.stdout.strip().split('\n', 1)[0]
    except (subprocess.SubprocessError, OSError):
        return ''


# ----------------------------- Main entrypoint -------------------------------


def run_cover_cfg(*,
                    input_tac: Path,
                    output_dir: Path,
                    config: CoverConfig = CoverConfig(),
                    z3_bin: Path | str | None = None,
                    ctac_bin: str = 'ctac',
                    cluster_z3_args: Sequence[str] = (),
                    abort_on_timeout: bool = False,
                    log: Sequence[Path] | None = None,
                    on_event: Callable[[str], None] | None = None,
                    ) -> CoverResult:
    """Run the CFG cover loop end-to-end.

    Writes artifacts to `output_dir`. Returns a `CoverResult` with
    paths to the manifest, rerun.sh, and report. The verdict is
    `'sat'`, `'unsat'`, or `'unknown'`.

    `on_event` is an optional progress callback fired with one-line
    status messages (cluster-solved, escape-found, completeness-OK,
    etc.); the CLI uses it to drive a live display."""
    t0 = time.time()
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    z3_path = resolve_z3_bin(z3_bin)
    notify = on_event or (lambda s: None)

    # Resolve INPUT_TAC to an absolute path for the certificate (the
    # audit script + verify-cover both need it independent of cwd).
    input_tac_abs = Path(input_tac).resolve()

    # Cover-wide metadata baked into the certificate.
    metadata = CoverMetadata(
        input_tac=str(input_tac_abs),
        z3_bin=str(z3_path),
        z3_version=_z3_version(z3_path),
        rw_flags=tuple(DEFAULT_RW_FLAGS),
        smt_flags=tuple(DEFAULT_SMT_FLAGS),
    )

    # Step 1: load CFG.
    info = load_cfg(Path(input_tac))
    notify(f'cfg: entry={info.entry} assert={info.assert_block} '
            f'blocks={info.graph.number_of_nodes()}')

    universe = blocks_on_entry_to_assert_paths(info)

    # Step 2: sample + saturate.
    paths = sample_paths(info, n=config.samples, seed=config.seed)
    paths = saturate_paths(info, paths, max_added=config.saturate_max_added)
    notify(f'paths: {len(paths)} sampled+saturated')

    # Step 3: cluster.
    k = config.k if config.k is not None else auto_k(len(paths))
    clusters = cluster_paths(paths, k=k, seed=config.seed)
    notify(f'clusters: {len(clusters)} (k={k})')

    # Step 4: materialize each cluster.
    states: list[ClusterState] = []
    for c in clusters:
        cluster_dir = output_dir / c.id
        try:
            arts = materialize_cluster(
                input_tac=input_tac,
                cluster_dir=cluster_dir,
                keep=c.keep_union,
                universe=universe,
                ctac_bin=ctac_bin,
            )
        except MaterializeError as e:
            notify(f'!! materialize {c.id} failed: {e.step}')
            raise
        states.append(ClusterState(cluster=c, artifacts=arts))
    notify(f'materialized: {len(states)} clusters')

    # Step 5: parallel solve clusters; first SAT wins.
    race_result = _solve_clusters_parallel(
        states, budget_s=config.cluster_budget_s,
        workers=config.workers, z3_bin=z3_path,
        cluster_z3_args=cluster_z3_args,
        abort_on_timeout=abort_on_timeout)

    # First-SAT exit.
    if race_result.winner is not None and race_result.winner_result.verdict == 'sat':
        winner_task = race_result.winner_task
        winner_result = race_result.winner_result
        winner_state = next(st for st in states
                              if st.cluster.id == winner_task.label)
        return _emit_sat_certificate(
            output_dir=output_dir,
            metadata=metadata,
            universe=universe,
            winner_state=winner_state,
            winner_result=winner_result,
            z3_path=z3_path,
            wall_s=time.time() - t0,
            n_completeness_iters=0,
        )
    for st in states:
        notify(f'cluster {st.cluster.id}: {st.verdict} ({st.wall_s:.2f}s)')

    # Soundness gate: the completeness loop's UnsatCertificate requires
    # every cluster covering a path to close UNSAT. If any cluster is
    # open (timeout/unknown/error), we can't claim a sound UNSAT.
    # Skip the loop, run the probe ONCE for diagnostic, and emit a
    # PartialResult so the user can see exactly what's missing.
    open_states = [s for s in states
                    if s.verdict not in ('sat', 'unsat')]
    if open_states:
        notify(f'soundness: {len(open_states)} of {len(states)} clusters '
                f'open ({", ".join(sorted({s.verdict or "?" for s in open_states}))}); '
                f'skipping completeness loop')
        return _emit_partial_result(
            output_dir=output_dir,
            metadata=metadata,
            universe=universe,
            info=info,
            states=states,
            z3_path=z3_path,
            completeness_budget_s=config.completeness_budget_s,
            wall_s=time.time() - t0,
            ctac_bin=ctac_bin,
            notify=notify,
        )

    # All clusters UNSAT → completeness loop is valid.
    # Step 6: completeness loop.
    completeness_dir = output_dir / 'completeness'
    completeness_dir.mkdir(parents=True, exist_ok=True)
    forbidden_paths: list[list[NBId]] = []
    forbidden_labels: list[str] = []
    cluster_keeps: list[frozenset[NBId]] = [st.cluster.keep_union
                                              for st in states]
    last_probe: Path | None = None
    last_probe_argv: tuple[str, ...] = ()
    last_probe_wall: float = 0.0

    for it in range(1, config.completeness_iter + 1):
        cluster_id_seq = [st.cluster.id for st in states]
        probe = emit_probe(info,
                             cluster_keeps=cluster_keeps,
                             forbidden_paths=forbidden_paths,
                             cluster_ids=cluster_id_seq,
                             forbidden_labels=forbidden_labels)
        probe_path = completeness_dir / f'probe_{it:03d}.smt2'
        probe_path.write_text(probe.smt2)

        verdict, wall, argv, stdout, _stderr = _solve_one(
            probe_path, budget_s=config.completeness_budget_s,
            z3_bin=z3_path)
        (completeness_dir / f'probe_{it:03d}.stdout').write_text(stdout)
        last_probe, last_probe_argv, last_probe_wall = (
            probe_path, tuple(argv), wall)

        if verdict == 'unsat':
            notify(f'completeness UNSAT at iter {it}; cover complete')
            return _emit_unsat_certificate(
                output_dir=output_dir,
                metadata=metadata,
                universe=universe,
                states=states,
                probe_path=probe_path,
                probe_argv=tuple(argv),
                probe_wall=wall,
                wall_s=time.time() - t0,
                n_completeness_iters=it,
            )
        if verdict != 'sat':
            notify(f'completeness unknown at iter {it}; bailing')
            break

        # SAT — derive the escape path.
        escape = derive_path_from_model(info, stdout)
        if escape is None:
            notify(f'completeness escape path unparseable at iter {it}; bailing')
            break
        notify(f'iter {it}: escape path len={len(escape)}')

        # 6a. Try absorption into a near-by cluster (UNSAT-only refinement).
        absorbed_state = try_absorb(
            states=states,
            escape=escape,
            absorb_threshold=config.absorb_threshold,
            absorb_budget_s=config.absorb_budget_s,
            universe=universe,
            input_tac=Path(input_tac),
            output_dir=output_dir,
            ctac_bin=ctac_bin,
            z3_bin=z3_path,
            cluster_z3_args=cluster_z3_args,
        )
        if absorbed_state is not None and absorbed_state.verdict == 'sat':
            return _emit_sat_certificate(
                output_dir=output_dir,
                metadata=metadata,
                universe=universe,
                winner_state=absorbed_state,
                winner_result=None,  # filled with recorded argv below
                z3_path=z3_path,
                wall_s=time.time() - t0,
                n_completeness_iters=it,
            )
        if absorbed_state is not None and absorbed_state.verdict == 'unsat':
            notify(f'iter {it}: absorbed into {absorbed_state.cluster.id}')
            # Update cluster_keeps so subsequent probes use widened set.
            cluster_keeps = [st.cluster.keep_union for st in states]
            forbidden_paths.append(escape)
            forbidden_labels.append(
                f'path_iter{it:03d}_absorbed_into_{absorbed_state.cluster.id}')
            continue

        # 6b. Singleton + core. Materialize π as its own cluster, solve
        # with --unsat-core, parse core blocks if UNSAT.
        singleton_id = f'cluster_esc_{it:03d}'
        singleton_dir = output_dir / singleton_id
        singleton_keep = frozenset(escape)
        try:
            arts = materialize_cluster(
                input_tac=input_tac,
                cluster_dir=singleton_dir,
                keep=singleton_keep,
                universe=universe,
                ctac_bin=ctac_bin,
                unsat_core=True,
            )
        except MaterializeError as e:
            notify(f'!! materialize singleton {singleton_id} failed: {e.step}')
            forbidden_paths.append(escape)
            continue

        # Singleton-from-escape IS a cluster (a 1-path one); honor
        # user z3 args. Completeness probe above is bare (custom theory).
        verdict_s, wall_s, argv_s, stdout_s, _ = _solve_one(
            arts.smt2, budget_s=config.cluster_budget_s,
            z3_bin=z3_path, extra_args=cluster_z3_args)

        sing_state = ClusterState(
            cluster=Cluster(id=singleton_id, members=(),
                              medoid=-1, keep_union=singleton_keep),
            artifacts=arts,
            verdict=verdict_s, wall_s=wall_s,
            z3_argv=tuple(argv_s),
        )
        states.append(sing_state)
        cluster_keeps.append(sing_state.cluster.keep_union)

        if verdict_s == 'sat':
            return _emit_sat_certificate(
                output_dir=output_dir,
                metadata=metadata,
                universe=universe,
                winner_state=sing_state,
                winner_result=None,
                z3_path=z3_path,
                wall_s=time.time() - t0,
                n_completeness_iters=it,
            )
        if verdict_s == 'unsat':
            core_blocks = core_blocks_from_stdout(stdout_s)
            if core_blocks:
                forbidden_paths.append(sorted(core_blocks))
                forbidden_labels.append(
                    f'core_iter{it:03d}_from_{singleton_id}')
                notify(f'iter {it}: singleton {singleton_id} UNSAT; '
                        f'core blocks={len(core_blocks)}')
            else:
                forbidden_paths.append(escape)
                forbidden_labels.append(
                    f'path_iter{it:03d}_no_core_{singleton_id}')
                notify(f'iter {it}: singleton UNSAT; no parseable core; '
                        f'forbid path-superset')
        else:
            forbidden_paths.append(escape)
            forbidden_labels.append(
                f'path_iter{it:03d}_{verdict_s}_{singleton_id}')
            notify(f'iter {it}: singleton {verdict_s}; forbid path-superset')

    # Step 7: max-iter reached (or completeness gave up). The loop
    # added singletons; some may not be UNSAT. Emit a partial result.
    return _emit_partial_result(
        output_dir=output_dir,
        metadata=metadata,
        universe=universe,
        info=info,
        states=states,
        z3_path=z3_path,
        completeness_budget_s=config.completeness_budget_s,
        wall_s=time.time() - t0,
        ctac_bin=ctac_bin,
        notify=notify,
        # The last probe ran inside the loop — reuse its verdict.
        recorded_probe_path=last_probe,
        recorded_probe_argv=last_probe_argv,
        recorded_probe_verdict=verdict if last_probe is not None else None,
        recorded_probe_wall=last_probe_wall,
    )


# ---------------------------- Certificate emit -------------------------------


def _emit_sat_certificate(*, output_dir: Path,
                            metadata: CoverMetadata,
                            universe: set,
                            winner_state: ClusterState,
                            winner_result: Z3RunResult | None,
                            z3_path: Path,
                            wall_s: float,
                            n_completeness_iters: int) -> CoverResult:
    """Write SAT cert + replay model + report + rerun.sh.

    The cert's `program_replay.tac_path` is INPUT_TAC (absolute) so the
    audit replays against the original program, not the slice."""
    # Re-solve with -model so we capture the model text the user can
    # validate via `ctac run --model`.
    smt2 = winner_state.artifacts.smt2
    res = solver_solve(smt2, timeout_s=60, z3_bin=z3_path,
                         extra_args=('-model',))
    model_text = res.stdout

    # Write the model text alongside the smt2 (cert paths are relative
    # to output_dir).
    model_path = winner_state.artifacts.cluster_dir / 'model.smt'
    model_path.write_text(model_text)

    # Parse simple (define-fun NAME () Int VAL) into a dict for the cert.
    import re
    z3_model: dict[str, str] = {}
    pat = re.compile(r'\(define-fun\s+(\S+)\s+\(\)\s+\S+\s+([^)]+)\)')
    for m in pat.finditer(model_text):
        z3_model[m.group(1).strip()] = m.group(2).strip()

    # Drops for the winning cluster (universe \ keep_union).
    drops = tuple(sorted(set(universe) - set(winner_state.cluster.keep_union)))

    # z3_args: persistent flags only, from the recorded argv.
    recorded_argv = (winner_result.argv if winner_result is not None
                       else (winner_state.z3_argv if winner_state.z3_argv
                              else res.argv))
    z3_args = _persistent_args(recorded_argv, smt2)

    manifest_path = output_dir / 'manifest.json'
    rerun_sh = output_dir / 'rerun.sh'

    cert = SatCertificate(
        metadata=metadata,
        sat_smt2=str(smt2.relative_to(output_dir)),
        winner_drops=drops,
        z3_model=z3_model,
        z3_args=z3_args,
        program_replay=ProgramReplayPlan(
            tac_path=metadata.input_tac,            # INPUT_TAC, not slice
            model_text_path=str(model_path.relative_to(output_dir)),
        ),
        rerun_sh='rerun.sh',
        witness_cluster=winner_state.cluster.id,
        wall_s=winner_state.wall_s,
    )
    save_certificate(cert, manifest_path)
    write_rerun_sh(cert, rerun_sh)

    report_path = output_dir / 'report.md'
    report_path.write_text(_render_sat_report(cert, winner_state, wall_s,
                                                 n_completeness_iters))

    return CoverResult(
        verdict='sat',
        manifest_path=manifest_path,
        report_path=report_path,
        rerun_sh_path=rerun_sh,
        wall_s=wall_s,
        n_clusters=0,  # SAT short-circuit; cluster count not informative
        n_completeness_iters=n_completeness_iters,
    )


def _emit_unsat_certificate(*, output_dir: Path,
                              metadata: CoverMetadata,
                              universe: set,
                              states: list[ClusterState],
                              probe_path: Path,
                              probe_argv: tuple[str, ...],
                              probe_wall: float,
                              wall_s: float,
                              n_completeness_iters: int) -> CoverResult:
    """Write UNSAT cert + report + rerun.sh."""
    # Copy the winning probe to probe_final.smt2 (stable name for
    # rerun.sh and verify-cover).
    final_probe = probe_path.parent / 'probe_final.smt2'
    if not final_probe.exists():
        shutil.copy2(probe_path, final_probe)

    sub_proofs = tuple(
        SubProof(
            sub_id=st.cluster.id,
            smt2=str(st.artifacts.smt2.relative_to(output_dir)),
            drops=tuple(sorted(set(universe) - set(st.cluster.keep_union))),
            z3_args=_persistent_args(st.z3_argv, st.artifacts.smt2),
            wall_s=st.wall_s,
        )
        for st in states if st.verdict == 'unsat'
    )
    decomposition = Decomposition(
        kind='cfg-cluster',
        clusters=tuple(
            ClusterRecord(
                id=st.cluster.id,
                keep_blocks=tuple(sorted(st.cluster.keep_union)),
                paths_covered=len(st.cluster.members),
            )
            for st in states if st.verdict == 'unsat'
        ),
    )
    cert = UnsatCertificate(
        metadata=metadata,
        decomposition=decomposition,
        sub_proofs=sub_proofs,
        completeness_proof=CompletenessProof(
            probe_smt2=str(final_probe.relative_to(output_dir)),
            z3_args=_persistent_args(probe_argv, probe_path),
            wall_s=probe_wall,
        ),
        rerun_sh='rerun.sh',
    )

    manifest_path = output_dir / 'manifest.json'
    rerun_sh = output_dir / 'rerun.sh'
    save_certificate(cert, manifest_path)
    write_rerun_sh(cert, rerun_sh)

    report_path = output_dir / 'report.md'
    report_path.write_text(_render_unsat_report(cert, states, wall_s,
                                                   n_completeness_iters))

    return CoverResult(
        verdict='unsat',
        manifest_path=manifest_path,
        report_path=report_path,
        rerun_sh_path=rerun_sh,
        wall_s=wall_s,
        n_clusters=len(states),
        n_completeness_iters=n_completeness_iters,
    )


def _emit_partial_result(*, output_dir: Path,
                            metadata: CoverMetadata,
                            universe: set,
                            info,
                            states: list[ClusterState],
                            z3_path: Path,
                            completeness_budget_s: int,
                            wall_s: float,
                            ctac_bin: str,
                            notify,
                            recorded_probe_path: Path | None = None,
                            recorded_probe_argv: tuple[str, ...] = (),
                            recorded_probe_verdict: str | None = None,
                            recorded_probe_wall: float = 0.0,
                            ) -> CoverResult:
    """Cover ran but didn't reach a sound sat/unsat verdict.

    Runs the completeness probe ONCE for diagnostic if it didn't run
    inside the (now-skipped or exhausted) completeness loop. Emits a
    PartialResult manifest that records every cluster's outcome plus
    the probe verdict, so the user can see exactly what needs more
    work."""
    import json as _json
    from ctac.solver.signature import DiagnosticSignature
    _ = ctac_bin  # reserved for future subgoal-emit refinements

    # Step A: ensure we have a probe outcome. If the partial flow
    # entered before the completeness loop ran, emit + solve a single
    # probe over the current cluster keeps for diagnostic only.
    completeness_dir = output_dir / 'completeness'
    completeness_dir.mkdir(parents=True, exist_ok=True)
    probe_outcome: ProbeOutcome | None = None
    if recorded_probe_path is not None and recorded_probe_verdict is not None:
        # Reuse the loop's last probe.
        final_probe = completeness_dir / 'probe_final.smt2'
        if not final_probe.exists():
            shutil.copy2(recorded_probe_path, final_probe)
        probe_outcome = ProbeOutcome(
            probe_smt2=str(final_probe.relative_to(output_dir)),
            verdict=recorded_probe_verdict,
            z3_args=_persistent_args(recorded_probe_argv, recorded_probe_path),
            wall_s=recorded_probe_wall,
        )
    else:
        # Single diagnostic probe.
        cluster_keeps = [st.cluster.keep_union for st in states]
        cluster_ids = [st.cluster.id for st in states]
        probe = emit_probe(info, cluster_keeps=cluster_keeps,
                             cluster_ids=cluster_ids)
        final_probe = completeness_dir / 'probe_final.smt2'
        final_probe.write_text(probe.smt2)
        notify('diagnostic probe: one-shot, no iteration')
        verdict, p_wall, p_argv, stdout, _ = _solve_one(
            final_probe, budget_s=completeness_budget_s, z3_bin=z3_path)
        (completeness_dir / 'probe_final.stdout').write_text(stdout)
        probe_outcome = ProbeOutcome(
            probe_smt2=str(final_probe.relative_to(output_dir)),
            verdict=verdict,
            z3_args=_persistent_args(p_argv, final_probe),
            wall_s=p_wall,
        )
        notify(f'diagnostic probe verdict: {verdict} ({p_wall:.2f}s)')

    # Step B: collect cluster outcomes (closed + open).
    cluster_outcomes = tuple(
        ClusterOutcome(
            sub_id=st.cluster.id,
            smt2=str(st.artifacts.smt2.relative_to(output_dir)),
            drops=tuple(sorted(set(universe) - set(st.cluster.keep_union))),
            verdict=st.verdict or 'unknown',
            z3_args=_persistent_args(st.z3_argv, st.artifacts.smt2),
            wall_s=st.wall_s,
        )
        for st in states
    )
    closed_sub_proofs = tuple(
        SubProof(
            sub_id=st.cluster.id,
            smt2=str(st.artifacts.smt2.relative_to(output_dir)),
            drops=tuple(sorted(set(universe) - set(st.cluster.keep_union))),
            z3_args=_persistent_args(st.z3_argv, st.artifacts.smt2),
            wall_s=st.wall_s,
        )
        for st in states if st.verdict == 'unsat'
    )

    # Step C: subgoals for open clusters.
    subgoals_dir = output_dir / 'subgoals'
    subgoals_dir.mkdir(parents=True, exist_ok=True)
    subgoals: list[Subgoal] = []
    for st in states:
        if st.verdict in ('sat', 'unsat'):
            continue
        sig = (DiagnosticSignature(
            label=st.signature_label or 'unknown',
            confidence=1.0,
            rationale='from cluster z3 -st snapshot',
            signals=st.signature or {},
        ) if st.signature_label else None)
        diag = classify(sig)
        smt2_rel = str(st.artifacts.smt2.relative_to(output_dir))
        sg = Subgoal(
            id=st.cluster.id,
            kind='cfg-cluster',
            smt2=smt2_rel,
            tac=str(st.artifacts.pinned_tac.relative_to(output_dir)),
            rw_tac=str(st.artifacts.rw_tac.relative_to(output_dir)),
            parent_vc=metadata.input_tac,
            rerun_cmd=' '.join(st.z3_argv) if st.z3_argv
                                                else f'ctac smt {smt2_rel} --run',
            hardness=diag,
            suggested_actions=tuple(suggest_actions(diag, smt2_path=smt2_rel)),
        )
        subgoals.append(sg)
        (subgoals_dir / f'{st.cluster.id}.json').write_text(
            _json.dumps(sg.to_json_dict(), indent=2, sort_keys=True) + '\n')

    # Step D: decide top-level verdict (timeout vs unknown).
    open_outcomes = [c for c in cluster_outcomes
                      if c.verdict not in ('sat', 'unsat')]
    has_unknown = any(c.verdict == 'unknown' for c in open_outcomes)
    has_unknown = has_unknown or (
        probe_outcome is not None and probe_outcome.verdict == 'unknown')
    top_verdict: Literal['timeout', 'unknown'] = (
        'unknown' if has_unknown else 'timeout')

    partial = PartialResult(
        metadata=metadata,
        verdict=top_verdict,
        cluster_outcomes=cluster_outcomes,
        closed_sub_proofs=closed_sub_proofs,
        probe_outcome=probe_outcome,
        rerun_sh='rerun.sh',
    )

    manifest_path = output_dir / 'manifest.json'
    save_certificate(partial, manifest_path)
    rerun_sh = output_dir / 'rerun.sh'
    write_rerun_sh(partial, rerun_sh)

    report_path = output_dir / 'report.md'
    report_path.write_text(_render_partial_report(partial, subgoals, wall_s))

    return CoverResult(
        verdict=top_verdict,
        manifest_path=manifest_path,
        report_path=report_path,
        rerun_sh_path=rerun_sh,
        wall_s=wall_s,
        n_clusters=len(states),
        n_completeness_iters=0,  # populated by caller via field after
        subgoals=subgoals,
    )


# --------------------------- Report rendering -------------------------------


def _render_sat_report(cert: SatCertificate, st: ClusterState,
                          wall_s: float, n_iters: int) -> str:
    return (
        '# ctac cover-cfg: SAT\n\n'
        f'- Witness cluster: `{cert.witness_cluster}`\n'
        f'- SAT smt2: `{cert.sat_smt2}`\n'
        f'- Wall time: {wall_s:.2f}s\n'
        f'- Completeness iters: {n_iters}\n\n'
        '## Reproduce\n\n'
        '```bash\n'
        './rerun.sh\n'
        '```\n\n'
        'The verdict is SAT iff the rerun script exits 0 (z3 confirms '
        'SAT on the slice, and `ctac run --validate` lifts the model '
        'back to an assert_fail in the original TAC).\n'
    )


def _render_unsat_report(cert: UnsatCertificate,
                            states: list[ClusterState],
                            wall_s: float, n_iters: int) -> str:
    lines = [
        '# ctac cover-cfg: UNSAT\n',
        f'- Clusters: {len(cert.sub_proofs)} (all UNSAT)',
        f'- Completeness iters: {n_iters}',
        f'- Wall time: {wall_s:.2f}s\n',
        '## Soundness\n',
        'Every CFG-feasible execution lies in some cluster whose VC is '
        'UNSAT; the completeness probe proves no path escapes the union '
        'of cluster keeps. See `durable/auto-cover-strategy.md` for the '
        'full argument.\n',
        '## Cluster decomposition\n',
        '| cluster | blocks | paths | wall |',
        '|---|---|---|---|',
    ]
    for c, st in zip(cert.decomposition.clusters, states):
        lines.append(f'| `{c.id}` | {len(c.keep_blocks)} | '
                       f'{c.paths_covered} | {st.wall_s:.2f}s |')
    lines.append('')
    lines.append('## Reproduce\n')
    lines.append('```bash')
    lines.append('./rerun.sh')
    lines.append('```\n')
    return '\n'.join(lines) + '\n'


def _render_partial_report(partial: PartialResult,
                              subgoals: list[Subgoal],
                              wall_s: float) -> str:
    lines = [
        f'# ctac cover-cfg: {partial.verdict.upper()} (partial)\n',
        f'- Top-level verdict: `{partial.verdict}`',
        f'- Total clusters: {len(partial.cluster_outcomes)}',
        f'- Closed UNSAT: {len(partial.closed_sub_proofs)}',
        f'- Open: {sum(1 for c in partial.cluster_outcomes if c.verdict not in ("sat","unsat"))}',
        f'- Wall time: {wall_s:.2f}s\n',
        '## Diagnosis (what still needs to close?)\n',
        f'- `clusters_need_closure` = **{partial.clusters_need_closure}**'
        '  (any open cluster verdict)',
        f'- `probe_needs_closure`   = **{partial.probe_needs_closure}**'
        '  (probe did not return UNSAT)',
        f'- `cover_is_incomplete`   = **{partial.cover_is_incomplete}**'
        '  (probe returned SAT → some CFG path escapes every cluster)\n',
    ]
    if partial.cover_is_incomplete:
        lines.append('### Action: cover is INCOMPLETE\n')
        lines.append('Sampling more paths or splitting tight clusters is '
                       'needed. Closing the open clusters alone is NOT '
                       'sufficient — the probe found an entry→assert path '
                       'that lies outside every cluster\'s keep.\n')
    elif partial.clusters_need_closure and not partial.probe_needs_closure:
        lines.append('### Action: more compute on open clusters\n')
        lines.append('The completeness probe closed UNSAT — the cover '
                       'decomposition is structurally complete. The open '
                       'clusters just need more solver budget (or a '
                       'tactic swap / seed sweep) to flip to UNSAT.\n')
    elif partial.clusters_need_closure and partial.probe_needs_closure:
        lines.append('### Action: both clusters AND probe need closure\n')
        lines.append('Some clusters are open and the diagnostic probe '
                       'didn\'t close UNSAT. Try first to close the '
                       'open clusters; the probe might close after those '
                       'are resolved (the loop adds singletons that '
                       'subsume escapes).\n')
    else:
        lines.append('### Action: probe didn\'t close (clusters are fine)\n')
        lines.append('All cluster sub-problems closed UNSAT, but the '
                       'completeness probe didn\'t close UNSAT. The cover '
                       'either has uncovered CFG paths (probe SAT) or '
                       'the probe budget was too tight (probe '
                       'timeout/unknown).\n')
    lines.append('## Cluster outcomes\n')
    lines.append('| cluster | verdict | wall | drops |')
    lines.append('|---|---|---|---|')
    for c in partial.cluster_outcomes:
        lines.append(f'| `{c.sub_id}` | `{c.verdict}` | {c.wall_s:.2f}s | '
                      f'{len(c.drops)} blocks |')
    if partial.probe_outcome is not None:
        p = partial.probe_outcome
        lines.append('')
        lines.append('## Probe outcome\n')
        lines.append(f'- smt2: `{p.probe_smt2}`')
        lines.append(f'- verdict: `{p.verdict}`')
        lines.append(f'- wall: {p.wall_s:.2f}s')
    if subgoals:
        lines.append('')
        lines.append('## Residual subgoals\n')
        lines.append('| id | hardness | confidence |')
        lines.append('|---|---|---|')
        for sg in subgoals:
            h = sg.hardness
            if h is None:
                lines.append(f'| `{sg.id}` | (no diagnosis) | - |')
            else:
                lines.append(
                    f'| `{sg.id}` | `{h.label}` | {h.confidence:.2f} |')
        lines.append('')
        lines.append('Per-subgoal action suggestions are in '
                       '`subgoals/<id>.json`.')
    return '\n'.join(lines) + '\n'
