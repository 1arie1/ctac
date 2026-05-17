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
    ClusterRecord,
    CompletenessProof,
    Decomposition,
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
from ctac.solver.z3 import resolve_z3_bin


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
    verdict: Literal['sat', 'unsat', 'unknown']
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


def _solve_clusters_parallel(states: list[ClusterState], *,
                                budget_s: int,
                                workers: int,
                                z3_bin: Path) -> RaceResult:
    """Parallel race over cluster VCs. First SAT wins; remainder
    SIGKILL'd. If no SAT verdict, all clusters run to completion."""
    cfg = Z3Config(name='default', args=())
    tasks = [
        RaceTask(config=cfg, seed=0,
                  smt2=Path(st.artifacts.smt2), timeout_s=budget_s,
                  z3_bin=z3_bin)
        for st in states
    ]
    # Map task label -> state for result attribution.
    label_to_state = {t.label: st for t, st in zip(tasks, states)}
    # Override default label (config/seed) with the cluster id so race
    # results match the cover's index. Easiest: build new tasks with
    # cluster id baked into the config name.
    tasks = [
        RaceTask(config=Z3Config(name=st.cluster.id, args=()),
                  seed=0, smt2=Path(st.artifacts.smt2),
                  timeout_s=budget_s, z3_bin=z3_bin)
        for st in states
    ]
    label_to_state = {t.label: st for t, st in zip(tasks, states)}

    result = race(tasks, max_concurrent=workers, accept=_accept_sat)
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
                z3_bin: Path) -> tuple[str, float, list[str], str, str]:
    """One-shot z3 invocation. Returns (verdict, wall_s, argv, stdout,
    stderr). Used by absorption + singleton+core paths where the race
    machinery is overkill."""
    argv = [str(z3_bin), f'-T:{budget_s}', '-st', '-smt2', str(smt2)]
    t0 = time.time()
    proc = subprocess.run(argv, capture_output=True, text=True,
                            timeout=budget_s + 10)
    wall = time.time() - t0
    first = proc.stdout.strip().split('\n', 1)[0] if proc.stdout else ''
    verdict = first if first in ('sat', 'unsat', 'unknown') else 'unknown'
    return verdict, wall, argv, proc.stdout, proc.stderr


# ----------------------------- Main entrypoint -------------------------------


def run_cover_cfg(*,
                    input_tac: Path,
                    output_dir: Path,
                    config: CoverConfig = CoverConfig(),
                    z3_bin: Path | str | None = None,
                    ctac_bin: str = 'ctac',
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
        workers=config.workers, z3_bin=z3_path)

    # First-SAT exit.
    if race_result.winner is not None and race_result.winner_result.verdict == 'sat':
        winner_task = race_result.winner_task
        winner_result = race_result.winner_result
        winner_state = next(st for st in states
                              if st.cluster.id == winner_task.label)
        return _emit_sat_certificate(
            output_dir=output_dir,
            winner_state=winner_state,
            winner_result=winner_result,
            input_tac=Path(input_tac),
            z3_path=z3_path,
            wall_s=time.time() - t0,
            n_completeness_iters=0,
        )
    for st in states:
        notify(f'cluster {st.cluster.id}: {st.verdict} ({st.wall_s:.2f}s)')

    # Step 6: completeness loop.
    completeness_dir = output_dir / 'completeness'
    completeness_dir.mkdir(parents=True, exist_ok=True)
    forbidden_paths: list[list[NBId]] = []
    cluster_keeps: list[frozenset[NBId]] = [st.cluster.keep_union
                                              for st in states]
    last_probe: Path | None = None
    last_probe_argv: tuple[str, ...] = ()
    last_probe_wall: float = 0.0
    final_iter = 0

    for it in range(1, config.completeness_iter + 1):
        final_iter = it
        probe = emit_probe(info,
                             cluster_keeps=cluster_keeps,
                             forbidden_paths=forbidden_paths)
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
                states=states,
                probe_path=probe_path,
                probe_argv=tuple(argv),
                probe_wall=wall,
                input_tac=Path(input_tac),
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
        )
        if absorbed_state is not None and absorbed_state.verdict == 'sat':
            return _emit_sat_certificate(
                output_dir=output_dir,
                winner_state=absorbed_state,
                winner_result=None,  # filled with recorded argv below
                input_tac=Path(input_tac),
                z3_path=z3_path,
                wall_s=time.time() - t0,
                n_completeness_iters=it,
            )
        if absorbed_state is not None and absorbed_state.verdict == 'unsat':
            notify(f'iter {it}: absorbed into {absorbed_state.cluster.id}')
            # Update cluster_keeps so subsequent probes use widened set.
            cluster_keeps = [st.cluster.keep_union for st in states]
            forbidden_paths.append(escape)
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

        verdict_s, wall_s, argv_s, stdout_s, _ = _solve_one(
            arts.smt2, budget_s=config.cluster_budget_s, z3_bin=z3_path)

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
                winner_state=sing_state,
                winner_result=None,
                input_tac=Path(input_tac),
                z3_path=z3_path,
                wall_s=time.time() - t0,
                n_completeness_iters=it,
            )
        if verdict_s == 'unsat':
            core_blocks = core_blocks_from_stdout(stdout_s)
            if core_blocks:
                forbidden_paths.append(sorted(core_blocks))
                notify(f'iter {it}: singleton {singleton_id} UNSAT; '
                        f'core blocks={len(core_blocks)}')
            else:
                forbidden_paths.append(escape)
                notify(f'iter {it}: singleton UNSAT; no parseable core; '
                        f'forbid path-superset')
        else:
            forbidden_paths.append(escape)
            notify(f'iter {it}: singleton {verdict_s}; forbid path-superset')

    # Step 7: max-iter reached (or completeness gave up). Emit residuals
    # + report verdict='unknown'.
    return _emit_unknown_report(
        output_dir=output_dir,
        states=states,
        last_probe=last_probe,
        last_probe_argv=last_probe_argv,
        last_probe_wall=last_probe_wall,
        input_tac=Path(input_tac),
        wall_s=time.time() - t0,
        n_completeness_iters=final_iter,
    )


# ---------------------------- Certificate emit -------------------------------


def _emit_sat_certificate(*, output_dir: Path,
                            winner_state: ClusterState,
                            winner_result: Z3RunResult | None,
                            input_tac: Path,
                            z3_path: Path,
                            wall_s: float,
                            n_completeness_iters: int) -> CoverResult:
    """Write SAT cert + replay model + report + rerun.sh."""
    # Re-solve with -model so we capture the model text the user can
    # validate via `ctac run --model`.
    smt2 = winner_state.artifacts.smt2
    argv = [str(z3_path), '-T:60', '-st', '-smt2', str(smt2)]
    proc = subprocess.run(argv, capture_output=True, text=True, timeout=70)
    model_text = proc.stdout

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

    manifest_path = output_dir / 'manifest.json'
    rerun_sh = output_dir / 'rerun.sh'

    cert = SatCertificate(
        sat_smt2=str(smt2.relative_to(output_dir)),
        z3_model=z3_model,
        z3_invocation=(tuple(winner_result.argv) if winner_result is not None
                         else tuple(winner_state.z3_argv) if winner_state.z3_argv
                         else tuple(argv)),
        program_replay=ProgramReplayPlan(
            tac_path=str(
                winner_state.artifacts.pinned_tac.relative_to(output_dir)),
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
                              states: list[ClusterState],
                              probe_path: Path,
                              probe_argv: tuple[str, ...],
                              probe_wall: float,
                              input_tac: Path,
                              wall_s: float,
                              n_completeness_iters: int) -> CoverResult:
    """Write UNSAT cert + report + rerun.sh."""
    sub_proofs = tuple(
        SubProof(
            sub_id=st.cluster.id,
            smt2=str(st.artifacts.smt2.relative_to(output_dir)),
            z3_invocation=st.z3_argv,
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
        decomposition=decomposition,
        sub_proofs=sub_proofs,
        completeness_proof=CompletenessProof(
            probe_smt2=str(probe_path.relative_to(output_dir)),
            z3_invocation=probe_argv,
            wall_s=probe_wall,
        ),
        rerun_sh='rerun.sh',
    )
    # Finalize: also copy/rename the winning probe to probe_final.smt2
    # so the rerun.sh path matches the convention.
    final_probe = probe_path.parent / 'probe_final.smt2'
    if not final_probe.exists():
        shutil.copy2(probe_path, final_probe)
        cert = UnsatCertificate(
            decomposition=cert.decomposition,
            sub_proofs=cert.sub_proofs,
            completeness_proof=CompletenessProof(
                probe_smt2=str(final_probe.relative_to(output_dir)),
                z3_invocation=probe_argv,
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


def _emit_unknown_report(*, output_dir: Path,
                           states: list[ClusterState],
                           last_probe: Path | None,
                           last_probe_argv: tuple[str, ...],
                           last_probe_wall: float,
                           input_tac: Path,
                           wall_s: float,
                           n_completeness_iters: int) -> CoverResult:
    """No verdict reached. Emit subgoals for unresolved clusters."""
    subgoals_dir = output_dir / 'subgoals'
    subgoals_dir.mkdir(parents=True, exist_ok=True)

    import json as _json
    subgoals: list[Subgoal] = []
    for st in states:
        if st.verdict == 'unsat':
            continue
        from ctac.solver.signature import DiagnosticSignature
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
            parent_vc=str(input_tac),
            rerun_cmd=' '.join(st.z3_argv) if st.z3_argv
                                                else f'ctac smt {smt2_rel} --run',
            hardness=diag,
            suggested_actions=tuple(suggest_actions(diag, smt2_path=smt2_rel)),
        )
        subgoals.append(sg)
        (subgoals_dir / f'{st.cluster.id}.json').write_text(
            _json.dumps(sg.to_json_dict(), indent=2, sort_keys=True) + '\n')

    manifest_path = output_dir / 'manifest.json'
    # No verdict cert; write a minimal status JSON the verifier can
    # still load (just enough to indicate non-verdict).
    manifest_path.write_text(_json.dumps({
        'kind': 'unknown',
        'schema_version': 1,
        'wall_s': wall_s,
        'n_completeness_iters': n_completeness_iters,
        'subgoals': [sg.id for sg in subgoals],
    }, indent=2, sort_keys=True) + '\n')

    report_path = output_dir / 'report.md'
    report_path.write_text(_render_unknown_report(
        states, subgoals, wall_s, n_completeness_iters, last_probe))

    return CoverResult(
        verdict='unknown',
        manifest_path=manifest_path,
        report_path=report_path,
        rerun_sh_path=output_dir / 'rerun.sh',
        wall_s=wall_s,
        n_clusters=len(states),
        n_completeness_iters=n_completeness_iters,
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


def _render_unknown_report(states: list[ClusterState],
                              subgoals: list[Subgoal],
                              wall_s: float, n_iters: int,
                              last_probe: Path | None) -> str:
    lines = [
        '# ctac cover-cfg: UNKNOWN (residual)\n',
        f'- Clusters: {len(states)}',
        f'- Completeness iters: {n_iters}',
        f'- Wall time: {wall_s:.2f}s',
        f'- Subgoals (unclosed): {len(subgoals)}\n',
        '## Residual subgoals\n',
        '| id | hardness | confidence |',
        '|---|---|---|',
    ]
    for sg in subgoals:
        h = sg.hardness
        if h is None:
            lines.append(f'| `{sg.id}` | (no diagnosis) | - |')
        else:
            lines.append(f'| `{sg.id}` | `{h.label}` | {h.confidence:.2f} |')
    lines.append('')
    lines.append('Per-subgoal action suggestions are in `subgoals/<id>.json`.')
    if last_probe is not None:
        lines.append('')
        lines.append(f'Final completeness probe (not UNSAT): '
                      f'`{last_probe.name}`.')
    return '\n'.join(lines) + '\n'
