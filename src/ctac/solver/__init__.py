"""ctac.solver — z3 client library.

This package is a generic z3 invocation layer with no dependency on
ctac's TAC pipeline. It provides:

- `z3` — low-level invocation (Z3Result, solve()).
- `runner` — streaming Z3Runner with progress events + abort policies.
- `signature` — bottleneck classifier (DiagnosticSignature).
- `config` — Z3Config (named cli-args bundle) + default configs.
- `race` — parallel orchestration with first-verdict-wins.

Higher-level strategies and the `ctac z3` CLI build on top of these
primitives.
"""
from __future__ import annotations

from ctac.solver.z3 import (
    Z3Result,
    solve,
    parse_final_stats,
)
from ctac.solver.runner import (
    Z3Runner,
    Z3RunResult,
    ProgressEvent,
    NlsatCall,
    AbortPolicy,
    parse_line,
    group_nlsat_calls,
)
from ctac.solver.signature import (
    DiagnosticSignature,
    infer_signature,
    SIG_FAST_CLOSE,
    SIG_ACTIVE,
    SIG_SLOWING,
    SIG_NLSAT_DIALOG,
    SIG_NLSAT_DOMINANT,
    SIG_NLSAT_STUCK,
    SIG_LP_BP_BLOWUP,
    SIG_PREPROCESSING,
    SIG_STUCK_UNKNOWN,
)
from ctac.solver.config import (
    Z3Config,
    DEFAULT_CONFIGS,
    discover_configs_file,
    load_configs_file,
    resolve_configs,
    save_winning_config,
)
from ctac.solver.race import (
    RaceTask,
    RaceResult,
    race,
)

__all__ = [
    # z3.py
    'Z3Result', 'solve', 'parse_final_stats',
    # runner.py
    'Z3Runner', 'Z3RunResult', 'ProgressEvent', 'NlsatCall', 'AbortPolicy',
    'parse_line', 'group_nlsat_calls',
    # signature.py
    'DiagnosticSignature', 'infer_signature',
    'SIG_FAST_CLOSE', 'SIG_ACTIVE', 'SIG_SLOWING',
    'SIG_NLSAT_DIALOG', 'SIG_NLSAT_DOMINANT', 'SIG_NLSAT_STUCK',
    'SIG_LP_BP_BLOWUP', 'SIG_PREPROCESSING', 'SIG_STUCK_UNKNOWN',
    # config.py
    'Z3Config', 'DEFAULT_CONFIGS', 'discover_configs_file',
    'load_configs_file', 'resolve_configs', 'save_winning_config',
    # race.py
    'RaceTask', 'RaceResult', 'race',
]
