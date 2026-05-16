"""Z3 configuration bundles — named (tactic, args) tuples.

A Z3Config is a named recipe for invoking z3: a label + a list of CLI
arguments that go AFTER `z3 -T:N -v:2 -st -smt2 <file>`. Seeds are
handled separately so the same config can be raced across seeds.

Examples:
  Z3Config('default', []) — default tactic.
  Z3Config('alt-tactic', ['tactic.default_tactic=(then simplify ... smt)']).
  Z3Config('bp-off', ['smt.arith.bprop_on_pivoted_rows=false']).
  Z3Config('qfnra-nlsat', ['tactic.default_tactic=(then qfnra-nlsat)']).

Discoverable config file: `.ctac-z3-configs.json` searched for in the
input file's directory and ancestors. Format:
  {
    "configs": [
      {"name": "my-config", "args": ["smt.arith.solver=2"]},
      ...
    ]
  }
"""
from __future__ import annotations

import json
import shlex
from dataclasses import dataclass, field
from pathlib import Path


@dataclass(frozen=True)
class Z3Config:
    """A named bundle of z3 CLI args. Seed and timeout are applied at
    invocation time, not stored here."""
    name: str
    args: tuple[str, ...] = field(default_factory=tuple)
    description: str = ''


    def __post_init__(self) -> None:
        # Normalize args to tuple even when constructed with a list.
        if not isinstance(self.args, tuple):
            object.__setattr__(self, 'args', tuple(self.args))

    def to_dict(self) -> dict:
        return {'name': self.name, 'args': list(self.args),
                 'description': self.description}

    @classmethod
    def from_dict(cls, d: dict) -> 'Z3Config':
        return cls(name=d['name'],
                    args=tuple(d.get('args', [])),
                    description=d.get('description', ''))

    def shell_args(self) -> str:
        """Args as a shell-quoted string for embedding in a rerun cmd."""
        return ' '.join(shlex.quote(a) for a in self.args)


# Default config set. Tuned to span the strategies that have been useful
# on the ctac corpus.
DEFAULT_CONFIGS: tuple[Z3Config, ...] = (
    Z3Config(
        name='default',
        args=(),
        description='z3 default tactic — first thing to try'),
    Z3Config(
        name='alt-then',
        args=('tactic.default_tactic=(then simplify propagate-values solve-eqs smt)',),
        description='preprocess-heavy then smt; useful when default stalls early'),
    Z3Config(
        name='qfnra-nlsat',
        args=('tactic.default_tactic=(then qfnra-nlsat)',),
        description='nonlinear-real-arith via nlsat directly; for heavy NLA'),
    Z3Config(
        name='bp-off',
        args=('smt.arith.bprop_on_pivoted_rows=false',),
        description='disable LP bound-propagation on pivoted rows; for lp-bp-aliasing'),
    Z3Config(
        name='no-propagate-eqs',
        args=('smt.arith.propagate_eqs=false',),
        description='disable simplex equality propagation; alternate lp-bp mitigation'),
    Z3Config(
        name='legacy-arith',
        args=('smt.arith.solver=2',),
        description='legacy arith solver (mixes signals differently)'),
)


def discover_configs_file(start: Path) -> Path | None:
    """Walk from `start` up the directory tree looking for a
    `.ctac-z3-configs.json` file. Returns the path or None."""
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while True:
        candidate = p / '.ctac-z3-configs.json'
        if candidate.is_file():
            return candidate
        if p.parent == p:
            return None
        p = p.parent


def load_configs_file(path: Path) -> list[Z3Config]:
    """Load configs from a JSON file. Format:
      {"configs": [{"name": "...", "args": [...], "description": "..."}]}
    """
    data = json.loads(path.read_text())
    return [Z3Config.from_dict(d) for d in data.get('configs', [])]


def resolve_configs(start: Path,
                     names: list[str] | None = None,
                     ) -> list[Z3Config]:
    """Resolve config names against defaults + discovered file.

    If `names` is None, returns ALL available configs (defaults + file).
    Otherwise filters to the named ones (file overrides defaults on
    name collision).
    """
    pool: dict[str, Z3Config] = {c.name: c for c in DEFAULT_CONFIGS}
    f = discover_configs_file(start)
    if f is not None:
        for c in load_configs_file(f):
            pool[c.name] = c   # file overrides default
    if names is None:
        return list(pool.values())
    missing = [n for n in names if n not in pool]
    if missing:
        raise KeyError(f'unknown config name(s): {missing}; '
                        f'available: {sorted(pool.keys())}')
    return [pool[n] for n in names]


def save_winning_config(config: Z3Config, path: Path) -> None:
    """Write a single Z3Config to a .json file in the same format
    consumed by load_configs_file (so it can be re-loaded later)."""
    path.write_text(json.dumps({'configs': [config.to_dict()]}, indent=2) + '\n')
