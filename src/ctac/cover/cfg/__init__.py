"""`ctac.cover.cfg` — CFG cover (path decomposition at TAC level).

Sound bottom-up cover for single-assert TAC VCs. See
``durable/auto-cover-strategy.md`` for the technique.

Architecture (modular, per the solver-infrastructure-design):

- `cfg_graph`    — load CFG into a networkx DiGraph; entry/assert IDs.
- `sampling`     — seeded random path sampling + path-through-block.
- `cluster`      — K-medoid + Hamming over path keep-sets.
- `completeness` — PB linear-path probe emitter + escape-path
                   derivation from the probe's model.
- `core_blocks`  — parse z3 (get-unsat-core); project to TAC block IDs.
- `materialize`  — pin/rw/smt for one cluster's wider sub-problem.
- `absorb`       — short-budget probe for cluster widening.
- `classify`     — per-cluster hardness diagnosis from z3 stats.
- `run`          — top-level orchestrator (the CEGAR loop).
"""
from __future__ import annotations
