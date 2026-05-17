"""Map a z3-runner `DiagnosticSignature` to a cover `HardnessDiagnosis`.

The two label taxonomies differ:

- `ctac.solver.signature.DiagnosticSignature` labels reflect z3's
  *observed* bottleneck (fast-close, lp-bp-blowup, nlsat-stuck, ...).
- `ctac.cover.HardnessDiagnosis` labels reflect the *recommended
  downstream tool* (nlsat-bottleneck, lp-bp-aliasing-memory,
  bytemap-uf-blowup, ...) per
  ``durable/auto-cover-strategy.md`` → "Beyond cover: triage by
  hardness reason".

This module is the thin glue: takes one, produces the other, plus
a list of `ActionSuggestion` entries hinting at next steps.
"""
from __future__ import annotations

from typing import Optional

from ctac.cover.subgoal import ActionSuggestion, HardnessDiagnosis, HardnessLabel
from ctac.solver.signature import DiagnosticSignature


_SIGNATURE_TO_HARDNESS: dict[str, HardnessLabel] = {
    # solver signature → cover hardness label
    'lp-bp-blowup':       'lp-bp-aliasing-memory',
    'nlsat-stuck':        'nlsat-bottleneck',
    'nlsat-dominant':     'nlsat-bottleneck',
    'nlsat-dialog':       'nlsat-bottleneck',
    'preprocessing-only': 'boolean-sat-only',
    # 'fast-close' / 'active-search' / 'slowing-down' / 'stuck-unknown'
    # → 'unknown' (handled by .get default)
}


def classify(sig: Optional[DiagnosticSignature],
              *, smt2_path: str | None = None) -> HardnessDiagnosis | None:
    """Convert a `DiagnosticSignature` to a `HardnessDiagnosis`.

    Returns None when the input is None (e.g. the cluster solver
    never produced a signature). Signature labels that don't map to
    a known hardness class become ``'unknown'`` with the original
    label in the rationale."""
    if sig is None:
        return None
    label = _SIGNATURE_TO_HARDNESS.get(sig.label, 'unknown')
    signals = {k: float(v) for k, v in sig.signals.items()
                if isinstance(v, (int, float))}
    rationale = sig.rationale
    if label == 'unknown' and sig.label != 'unknown':
        rationale = f'(z3 signature: {sig.label}) {rationale}'
    return HardnessDiagnosis(
        label=label,
        confidence=sig.confidence,
        signature=signals,
        rationale=rationale.strip(),
    )


def suggest_actions(diag: HardnessDiagnosis | None,
                      *, smt2_path: str) -> list[ActionSuggestion]:
    """Return ready-to-run action suggestions for a hardness class.

    Tied to the taxonomy in ``durable/auto-cover-strategy.md``:
    each label has a canonical first-attempt solver knob or
    sub-tool."""
    if diag is None:
        return []
    label = diag.label
    if label == 'nlsat-bottleneck':
        return [
            ActionSuggestion(
                label='retry with seed rotation',
                command=f'ctac z3 {smt2_path} --seeds 0-7 -j 4',
                expected_payoff='one seed may dodge the nlsat trap'),
            ActionSuggestion(
                label='alt tactic',
                command=f'ctac z3 {smt2_path} '
                          '--configs default,alt-then --seeds 0-3',
                expected_payoff='solver gets to a different polynomial '
                                  'subproblem'),
        ]
    if label == 'lp-bp-aliasing-memory':
        return [
            ActionSuggestion(
                label='throttle LP bound-propagation',
                command=f'ctac z3 {smt2_path} -- '
                          'smt.arith.bprop_on_pivoted_rows=false',
                expected_payoff='disables the LP pivot bprop loop'),
            ActionSuggestion(
                label='alternative arith propagation',
                command=f'ctac z3 {smt2_path} -- '
                          'smt.arith.propagation_mode=0',
                expected_payoff='disables arith propagation entirely'),
        ]
    if label == 'bytemap-uf-blowup':
        return [
            ActionSuggestion(
                label='re-emit with --store-reduce',
                command='ctac smt <tac> --store-reduce -o reduced.smt2',
                expected_payoff='shorten the Store-over-Store chain'),
        ]
    if label == 'boolean-sat-only':
        return [
            ActionSuggestion(
                label='swap to a simpler tactic',
                command=f'ctac z3 {smt2_path} '
                          '--configs default,then-simplify',
                expected_payoff='Boolean SAT often closes under '
                                  'plain solver chain'),
        ]
    return []
