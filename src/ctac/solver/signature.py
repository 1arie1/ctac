"""Bottleneck signature inference for Z3Runner timelines.

Pipeline:
  events + final stats + verdict → features → cascading classifier →
  DiagnosticSignature (label, confidence, runner_up, margin,
                       rationale, signals, suggested_actions)

Priority cascade — more specific bottleneck labels win over generic
observations even if the generic rule has higher signal strength. The
margin to the runner-up exposes borderline cases.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Any

from ctac.solver.runner import ProgressEvent, group_nlsat_calls


# ---- Signature labels -------------------------------------------------------

SIG_FAST_CLOSE = 'fast-close'
SIG_ACTIVE = 'active-search'
SIG_SLOWING = 'slowing-down'
SIG_NLSAT_DIALOG = 'nlsat-dialog'
SIG_NLSAT_DOMINANT = 'nlsat-dominant'
SIG_NLSAT_STUCK = 'nlsat-stuck'
SIG_LP_BP_BLOWUP = 'lp-bp-blowup'
SIG_PREPROCESSING = 'preprocessing-only'
SIG_STUCK_UNKNOWN = 'stuck-unknown'


@dataclass
class DiagnosticSignature:
    label: str
    confidence: float
    rationale: str
    signals: dict[str, Any] = field(default_factory=dict)
    suggested_actions: list[str] = field(default_factory=list)
    runner_up: tuple[str, float] | None = None
    margin: float | None = None


# ---- Helpers ----------------------------------------------------------------

def _clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))


def _rate(stats_events: list[ProgressEvent], field_name: str) -> float:
    """(delta field) / (delta wall) over a sequence of smt-stats events.

    Floors dt at 0.1s so the first-two-samples-at-same-instant case
    doesn't blow up the rate."""
    if len(stats_events) < 2:
        return 0.0
    first = stats_events[0]
    last = stats_events[-1]
    dt = max(last.wall_s - first.wall_s, 0.1)
    return (last.payload[field_name] - first.payload[field_name]) / dt


def _nlsat_interleaving(events: list[ProgressEvent]) -> dict:
    """Count nlsat-line runs between consecutive smt-stats events.

    Returns:
      max_nlsat_run — largest consecutive nlsat-line count between
                       two smt-stats samples.
      mean_nlsat_run, n_intervals, total_nlsat, ratio (nlsat/smt).
    """
    runs: list[int] = []
    current = 0
    n_smt = 0
    total_nlsat = 0
    for e in events:
        if e.kind == 'smt-stats':
            n_smt += 1
            if n_smt >= 2:
                runs.append(current)
            current = 0
        elif e.kind == 'nlsat-line':
            current += 1
            total_nlsat += 1
    return {
        'max_nlsat_run': max(runs) if runs else 0,
        'mean_nlsat_run': sum(runs) / len(runs) if runs else 0.0,
        'n_intervals': len(runs),
        'total_nlsat': total_nlsat,
        'ratio': total_nlsat / max(n_smt, 1),
    }


# ---- Signal-strength functions ---------------------------------------------

def _strength_fast_close(wall_s: float, n_smt_stats: int) -> float:
    wall_score = _clamp(1.0 - wall_s / 5.0, 0.0, 1.0)
    samples_score = _clamp(1.0 - n_smt_stats / 4.0, 0.0, 1.0)
    return _clamp(0.7 + 0.3 * (wall_score + samples_score) / 2.0, 0.5, 0.99)


def _strength_lp_bp_4stat(lp_bp: float, diseq: float,
                            lower_plus_upper: float,
                            decisions: float,
                            conflicts: float) -> tuple[float, int]:
    """4-stat lp-bp signature from auto-cover-strategy.md.

    Returns (confidence, n_signals_matched). Base confidence from
    primary signal's ratio; +0.075 bonus per additional signal."""
    flag_a = lp_bp > 1e6
    flag_b = diseq > 1e6
    flag_c = lower_plus_upper > 1e6
    decisions_to_conflicts = decisions / max(conflicts, 1.0)
    flag_d = decisions_to_conflicts > 100
    n_signals = int(flag_a) + int(flag_b) + int(flag_c) + int(flag_d)
    ratio = lp_bp / max(conflicts, 1.0)
    base = 0.4 + 0.1 * math.log10(max(ratio, 1.0))
    bonus = 0.075 * (n_signals - 1) if n_signals > 1 else 0.0
    return _clamp(base + bonus, 0.55, 0.97), n_signals


def _strength_nlsat_stuck(n_lines: int, conflicts_delta: int) -> float:
    return _clamp(0.5 + 0.04 * (n_lines - 3) + 0.015 * conflicts_delta,
                   0.6, 0.97)


def _strength_nlsat_dominant(max_run: int, ratio: float) -> float:
    run_score = _clamp(max_run / 50.0, 0.0, 1.0)
    ratio_score = _clamp(ratio / 20.0, 0.0, 1.0)
    return _clamp(0.5 + 0.45 * (run_score + ratio_score) / 2.0, 0.55, 0.95)


def _strength_nlsat_dialog(n_calls: int, max_run: int, ratio: float) -> float:
    call_score = _clamp(n_calls / 50.0, 0.3, 1.0)
    interleave_score = _clamp(1.0 - max_run / 15.0, 0.3, 1.0)
    return _clamp(0.5 + 0.35 * (call_score + interleave_score) / 2.0,
                   0.55, 0.90)


def _strength_slowing_down(early_rate: float, late_rate: float) -> float:
    if early_rate <= 0:
        return 0.5
    drop = 1.0 - (late_rate / early_rate)
    return _clamp(0.5 + 0.4 * drop, 0.55, 0.9)


def _strength_active_search(late_rate: float) -> float:
    return _clamp(0.5 + 0.05 * math.log10(max(late_rate, 1.0)), 0.55, 0.85)


# ---- Classifier -------------------------------------------------------------

def infer_signature(events: list[ProgressEvent],
                     final_stats: dict[str, float] | None,
                     wall_s: float,
                     verdict: str) -> DiagnosticSignature:
    """Run the cascading classifier; return top signature + runner-up.

    Rules are evaluated in priority order. Top match = first (highest-
    priority) match. Runner-up = second matching rule. Confidence
    within each match reflects signal strength.

    Margin = top.confidence - runner_up.confidence. Negative margin
    flags borderline cases where a generic rule had stronger signal
    but was preempted by priority of specificity."""
    smt_stats_evs = [e for e in events if e.kind == 'smt-stats']
    nlsat_calls = group_nlsat_calls(events)
    tactic_starts = [e for e in events if e.kind == 'tactic-start']
    smt_searching_seen = any(e.payload.get('tactic') == 'smt.searching'
                              for e in tactic_starts)
    final_stats = final_stats or {}
    lp_bp = final_stats.get('arith-bound-propagations-lp', 0)
    f_conflicts = final_stats.get('conflicts', 0)
    f_diseq = final_stats.get('arith-diseq', 0)
    f_lower = final_stats.get('arith-lower', 0)
    f_upper = final_stats.get('arith-upper', 0)
    f_decisions = final_stats.get('decisions', 0)
    stuck_calls = [c for c in nlsat_calls if c.is_stuck]
    last_call_stuck = bool(nlsat_calls) and nlsat_calls[-1].is_stuck
    n_smt = len(smt_stats_evs)
    nlsat_interleave = _nlsat_interleaving(events)

    matches: list[DiagnosticSignature] = []

    # Rule 1: preprocessing-only
    if not smt_searching_seen and verdict in ('timeout', 'unknown'):
        matches.append(DiagnosticSignature(
            label=SIG_PREPROCESSING, confidence=0.9,
            rationale='(smt.searching) never observed; preprocessing consumed the budget',
            signals={'wall_s': wall_s, 'smt_stats_count': 0},
            suggested_actions=['reduce VC size or disable expensive tactics']))

    # Rule 2: fast-close
    if verdict in ('sat', 'unsat') and wall_s < 5 and n_smt <= 3:
        conf = _strength_fast_close(wall_s, n_smt)
        matches.append(DiagnosticSignature(
            label=SIG_FAST_CLOSE, confidence=conf,
            rationale=f'verdict={verdict} after {n_smt} stats samples in {wall_s:.2f}s',
            signals={'wall_s': wall_s, 'smt_stats_count': n_smt},
            suggested_actions=['commit verdict; no further work']))

    # Rule 3: lp-bp-blowup (4-stat signature)
    if verdict in ('timeout', 'unknown') and lp_bp > 1e6:
        conf, n_signals = _strength_lp_bp_4stat(
            lp_bp, f_diseq, f_lower + f_upper, f_decisions, f_conflicts)
        d_over_c = f_decisions / max(f_conflicts, 1)
        matches.append(DiagnosticSignature(
            label=SIG_LP_BP_BLOWUP, confidence=conf,
            rationale=(f'4-stat: lp-bp={lp_bp:.0f}, diseq={f_diseq:.0f}, '
                        f'lower+upper={f_lower + f_upper:.0f}, '
                        f'dec/confl={d_over_c:.0f} ({n_signals}/4 signals)'),
            signals={'lp_bp': lp_bp, 'diseq': f_diseq,
                     'lower_plus_upper': f_lower + f_upper,
                     'decisions_per_conflict': d_over_c,
                     'n_signals_matched': n_signals},
            suggested_actions=['abandon strategy; route to alias-cover']))

    # Rule 4: nlsat-stuck (b&b dead-end)
    if verdict in ('timeout', 'unknown') and last_call_stuck:
        last = nlsat_calls[-1]
        d_confl = last.lines[-1]['conflicts'] - last.lines[0]['conflicts']
        conf = _strength_nlsat_stuck(last.n_lines, d_confl)
        matches.append(DiagnosticSignature(
            label=SIG_NLSAT_STUCK, confidence=conf,
            rationale=(f'last nlsat call has {last.n_lines} lines, '
                        f'conflicts {last.lines[0]["conflicts"]}→{last.lines[-1]["conflicts"]} '
                        '(still in progress at termination)'),
            signals={'n_stuck_calls': len(stuck_calls),
                     'last_call_lines': last.n_lines,
                     'last_call_conflicts_delta': d_confl},
            suggested_actions=['retry with seed rotation (parallel via lemur-sweep)']))

    # Rule 5a: nlsat-dominant (long nlsat runs between smt-stats)
    if len(nlsat_calls) >= 10 and not last_call_stuck and \
       nlsat_interleave['max_nlsat_run'] >= 15:
        conf = _strength_nlsat_dominant(nlsat_interleave['max_nlsat_run'],
                                          nlsat_interleave['ratio'])
        action = ('budget likely insufficient; consider tactic change or seed rotation'
                   if verdict in ('timeout', 'unknown')
                   else 'closed despite NLA dominance; commit verdict')
        matches.append(DiagnosticSignature(
            label=SIG_NLSAT_DOMINANT, confidence=conf,
            rationale=(f'{len(nlsat_calls)} nlsat calls, max run of '
                        f'{nlsat_interleave["max_nlsat_run"]} nlsat lines between smt-stats '
                        f'(ratio {nlsat_interleave["ratio"]:.1f}× nlsat/smt)'),
            signals={'n_calls': len(nlsat_calls),
                     'max_nlsat_run': nlsat_interleave['max_nlsat_run'],
                     'nlsat_smt_ratio': nlsat_interleave['ratio']},
            suggested_actions=[action]))

    # Rule 5b: nlsat-dialog (well-interleaved nlsat dispatch)
    if len(nlsat_calls) >= 10 and not last_call_stuck and \
       nlsat_interleave['max_nlsat_run'] < 15:
        avg_lines = sum(c.n_lines for c in nlsat_calls) / len(nlsat_calls)
        conf = _strength_nlsat_dialog(len(nlsat_calls),
                                        nlsat_interleave['max_nlsat_run'],
                                        nlsat_interleave['ratio'])
        action = ('more budget; smt-nlsat communication healthy, z3 making progress'
                   if verdict in ('timeout', 'unknown')
                   else 'expected behavior; commit verdict')
        matches.append(DiagnosticSignature(
            label=SIG_NLSAT_DIALOG, confidence=conf,
            rationale=(f'{len(nlsat_calls)} nlsat calls, max run '
                        f'{nlsat_interleave["max_nlsat_run"]} nlsat-lines between smt-stats '
                        '(interleaved dialog)'),
            signals={'n_calls': len(nlsat_calls),
                     'max_nlsat_run': nlsat_interleave['max_nlsat_run'],
                     'avg_lines_per_call': avg_lines},
            suggested_actions=[action]))

    # Rule 6: slowing-down
    if n_smt >= 4:
        mid = n_smt // 2
        early = smt_stats_evs[:mid]
        late = smt_stats_evs[mid:]
        er = _rate(early, 'conflicts')
        lr = _rate(late, 'conflicts')
        if er > 10 and lr < 0.3 * er:
            conf = _strength_slowing_down(er, lr)
            matches.append(DiagnosticSignature(
                label=SIG_SLOWING, confidence=conf,
                rationale=f'conflict rate dropped {er:.1f}/s → {lr:.1f}/s',
                signals={'early_rate': er, 'late_rate': lr},
                suggested_actions=['extend budget marginally; consider tactic change']))

    # Rule 7: active-search (catch-all "running")
    if n_smt >= 3:
        mid = n_smt // 2
        late = smt_stats_evs[mid:]
        lr = _rate(late, 'conflicts')
        if lr > 0:
            conf = _strength_active_search(lr)
            matches.append(DiagnosticSignature(
                label=SIG_ACTIVE, confidence=conf,
                rationale=f'steady conflict rate ~{lr:.1f}/s; verdict={verdict}',
                signals={'late_rate': lr},
                suggested_actions=['wait within budget']))

    # Fallback
    if not matches:
        matches.append(DiagnosticSignature(
            label=SIG_STUCK_UNKNOWN, confidence=0.4,
            rationale=f'verdict={verdict}, smt_stats={n_smt}, nlsat_calls={len(nlsat_calls)}',
            signals={'wall_s': wall_s, 'smt_stats_count': n_smt,
                     'n_nlsat_calls': len(nlsat_calls)},
            suggested_actions=['dump full timeline; manual inspection']))

    # Top = highest-PRIORITY match (matches list is in priority order).
    # Runner-up = second highest-priority match.
    top = matches[0]
    if len(matches) > 1:
        ru = matches[1]
        top = DiagnosticSignature(
            label=top.label, confidence=top.confidence,
            rationale=top.rationale, signals=top.signals,
            suggested_actions=top.suggested_actions,
            runner_up=(ru.label, ru.confidence),
            margin=top.confidence - ru.confidence)
    return top
