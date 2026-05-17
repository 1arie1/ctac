"""CFG-completeness probe: pseudo-boolean linear-path encoding.

The probe asks: "does any feasible entry→assert CFG path *escape*
every cluster's keep AND every previously-found path?"

UNSAT means no such escape exists ⇒ every CFG-feasible execution is
covered by some cluster (the completeness certificate).

SAT means at least one escape exists ⇒ derive the path, fold it into
the cover (absorb or singleton+core), and re-probe.

Encoding (per ``durable/auto-cover-strategy.md``, the PB section):

- Vars
  - ``BLK_<bid>`` Bool — true iff block ``bid`` lies on the path.
  - ``e_<u>__TO__<v>`` Bool — true iff edge (u,v) lies on the path.
    Separator ``__TO__`` disambiguates block IDs that themselves
    contain underscores (like ``"4_2_1_0_0_0"``).

- Structural constraints
  - ``BLK_entry`` and ``BLK_assert`` pinned true.
  - For each edge (u,v): ``e_uv => (BLK_u AND BLK_v)``.
  - For each block v != entry with non-empty in-edges:
    ``BLK_v => ((_ pbeq 1 1 ... 1) e_in1 e_in2 ...)`` (exactly-one).
    Plus ``((_ at-most 1) e_in1 ...)`` unconditionally — cheap BCP fuel.
  - For each block v != assert with non-empty out-edges:
    ``BLK_v => ((_ pbeq 1 1 ... 1) e_out1 e_out2 ...)``.
  - Blocks with no in-edges (and not entry) or no out-edges (and not
    assert) forced false.
  - In-edges of entry and out-edges of assert pinned false (the path
    is strictly entry→assert).

- PB disjunctions
  - Per-cluster *escape*:
    ``((_ at-least 1) BLK_b ...)`` for ``b ∈ D_i``
    (D_i = drop-set = blocks NOT in cluster i's keep).
  - Forbid past path-supersets:
    ``((_ at-most |bs|-1) BLK_b ...)`` for ``b ∈ forbidden``.

- Logic: ``(set-logic ALL)`` — z3 needs ALL to accept the
  pseudo-boolean operators.

The probe is tiny (~B + E Booleans on a CFG with B blocks / E edges);
z3 typically returns a verdict in milliseconds.
"""
from __future__ import annotations

import re
from collections.abc import Iterable, Sequence
from dataclasses import dataclass

import networkx as nx

from ctac.cover.cfg.cfg_graph import CfgInfo
from ctac.ir.models import NBId


_EDGE_SEP = '__TO__'


def edge_var(u: NBId, v: NBId) -> str:
    """Edge-on-path Boolean variable name."""
    return f'e_{u}{_EDGE_SEP}{v}'


def block_var(b: NBId) -> str:
    """Block-on-path Boolean variable name."""
    return f'BLK_{b}'


_EDGE_VAR_RE = re.compile(
    rf'^e_(?P<u>.+?){re.escape(_EDGE_SEP)}(?P<v>.+)$'
)


def _fmt_block_list(blocks: list[NBId], *, max_inline: int = 8) -> str:
    """Pretty-print a list of block ids for audit comments. If the list
    is short, comma-separated inline; otherwise truncated with '...'."""
    if not blocks:
        return '[]'
    if len(blocks) <= max_inline:
        return '[' + ', '.join(blocks) + ']'
    head = ', '.join(blocks[:max_inline])
    return f'[{head}, ... ({len(blocks) - max_inline} more)]'


def parse_edge_var(name: str) -> tuple[NBId, NBId] | None:
    """Inverse of `edge_var`. Returns (u, v) or None if not an edge var."""
    m = _EDGE_VAR_RE.match(name)
    if not m:
        return None
    return m.group('u'), m.group('v')


# ----------------------------- Probe emitter --------------------------------


@dataclass(frozen=True)
class CompletenessProbe:
    """The emitted probe + the variable namespace it uses."""

    smt2: str
    block_vars: tuple[str, ...]
    edge_vars: tuple[str, ...]


def emit_probe(info: CfgInfo, *,
                 cluster_keeps: Sequence[Iterable[NBId]] = (),
                 forbidden_paths: Sequence[Iterable[NBId]] = (),
                 cluster_ids: Sequence[str] = (),
                 forbidden_labels: Sequence[str] = (),
                 ) -> CompletenessProbe:
    """Emit the completeness probe smt2 text.

    `cluster_keeps` is a sequence of keep-sets (one per cluster).
    The probe asserts: for each cluster i, the path visits at least
    one block in `(all_path_blocks) \\ keep_i`.

    `forbidden_paths` is a sequence of past escape-paths (block lists
    or sets); the probe asserts no future path is a superset of any
    forbidden one (at-most-(|fp|-1) of its blocks may be on the path).

    `cluster_ids` and `forbidden_labels` are optional human-readable
    labels written into the smt2 comments alongside each constraint.
    When omitted, the probe falls back to numeric indices. The labels
    are essential for manual audit: each escape / forbid block carries
    `; cluster_<id>: drops = [b1, b2, ...]` and similar, so a reader
    can confirm the probe encodes the right thing without re-running
    the cover.
    """
    g = info.graph
    entry = info.entry
    assert_b = info.assert_block

    # Universe: blocks on at least one entry-to-assert path. Off-path
    # blocks contribute neither in-edges nor out-edges to the probe.
    forward = set(nx.descendants(g, entry)) | {entry}
    backward = set(nx.ancestors(g, assert_b)) | {assert_b}
    blocks = sorted(forward & backward)
    if entry not in blocks:
        blocks.insert(0, entry)
    if assert_b not in blocks:
        blocks.append(assert_b)

    # Edges restricted to the universe.
    edges = [(u, v) for u, v in g.edges
              if u in blocks and v in blocks]

    # Cluster drop-sets (D_i = universe \ keep_i).
    universe_set = set(blocks)
    drop_sets: list[list[NBId]] = []
    for ki in cluster_keeps:
        d = sorted(universe_set - set(ki))
        drop_sets.append(d)

    # Build smt2
    out: list[str] = []
    out.append('(set-logic ALL)')
    out.append('; --- block-on-path variables ---')
    for b in blocks:
        out.append(f'(declare-const {block_var(b)} Bool)')
    out.append('; --- edge-on-path variables ---')
    for u, v in edges:
        out.append(f'(declare-const {edge_var(u, v)} Bool)')

    # Pin entry / assert blocks true.
    out.append('; --- entry / assert pinned ---')
    out.append(f'(assert {block_var(entry)})')
    out.append(f'(assert {block_var(assert_b)})')

    # e_uv => (BLK_u AND BLK_v).
    out.append('; --- edge implies endpoints ---')
    for u, v in edges:
        ev = edge_var(u, v)
        out.append(
            f'(assert (=> {ev} (and {block_var(u)} {block_var(v)})))')

    # Out-edges and in-edges per block.
    out_edges: dict[NBId, list[tuple[NBId, NBId]]] = {b: [] for b in blocks}
    in_edges: dict[NBId, list[tuple[NBId, NBId]]] = {b: [] for b in blocks}
    for u, v in edges:
        out_edges[u].append((u, v))
        in_edges[v].append((u, v))

    out.append('; --- in-edges: exactly-one when block is on path ---')
    for v in blocks:
        if v == entry:
            # Entry has no in-edges on the path.
            for e in in_edges.get(v, []):
                out.append(f'(assert (not {edge_var(*e)}))')
            continue
        ins = in_edges.get(v, [])
        if not ins:
            # Non-entry block with no in-edges in the universe is
            # unreachable on any entry→assert path; force off.
            out.append(f'(assert (not {block_var(v)}))')
            continue
        ev_names = [edge_var(*e) for e in ins]
        # BLK_v => pbeq 1 of in-edges
        # Use ((_ pbeq 1 1 1 ...) e1 e2 ...) — coeffs first then args.
        coeffs = ' '.join('1' for _ in ev_names)
        body = ' '.join(ev_names)
        out.append(
            f'(assert (=> {block_var(v)} '
            f'((_ pbeq 1 {coeffs}) {body})))')
        # Plus unconditional at-most-1 (cheap BCP).
        if len(ev_names) >= 2:
            out.append(
                f'(assert ((_ at-most 1) {body}))')

    out.append('; --- out-edges: exactly-one when block is on path ---')
    for u in blocks:
        if u == assert_b:
            # Assert has no out-edges on the path.
            for e in out_edges.get(u, []):
                out.append(f'(assert (not {edge_var(*e)}))')
            continue
        outs = out_edges.get(u, [])
        if not outs:
            # Non-assert block with no out-edges has no successor on
            # any entry→assert path; force off.
            out.append(f'(assert (not {block_var(u)}))')
            continue
        ev_names = [edge_var(*e) for e in outs]
        coeffs = ' '.join('1' for _ in ev_names)
        body = ' '.join(ev_names)
        out.append(
            f'(assert (=> {block_var(u)} '
            f'((_ pbeq 1 {coeffs}) {body})))')

    # Cluster escape disjunctions.
    if drop_sets:
        out.append('; ---------------------------------------------------------')
        out.append('; Per-cluster escape: any path must visit at least one')
        out.append('; block in each cluster\'s drop set D_i = universe \\ keep_i.')
        out.append('; ---------------------------------------------------------')
        for i, d in enumerate(drop_sets):
            label = cluster_ids[i] if i < len(cluster_ids) else f'cluster_{i}'
            keep_i = sorted(set(cluster_keeps[i])) if i < len(cluster_keeps) else []
            out.append('')
            out.append(f'; --- {label} ---')
            out.append(f';   keep ({len(keep_i)} blocks):  '
                         f'{_fmt_block_list(keep_i)}')
            out.append(f';   drop ({len(d)} blocks):  '
                         f'{_fmt_block_list(d)}')
            if not d:
                out.append(f'(assert false) ; {label}: keep is universal '
                             f'(no escape possible)')
                continue
            body = ' '.join(block_var(b) for b in d)
            out.append(
                f'(assert ((_ at-least 1) {body})) ; {label}: escape D')

    # Forbid past-path supersets.
    if forbidden_paths:
        out.append('')
        out.append('; ---------------------------------------------------------')
        out.append('; Forbid supersets of prior escape paths / unsat-core block')
        out.append('; sets. Each (_ at-most n-1 ...) clause says: not all n')
        out.append('; blocks of the prior path can be on a future path together.')
        out.append('; ---------------------------------------------------------')
        for j, fp in enumerate(forbidden_paths):
            blocks_fp = sorted(set(fp) & universe_set)
            if not blocks_fp:
                continue
            label = (forbidden_labels[j] if j < len(forbidden_labels)
                       else f'path_{j}')
            n = len(blocks_fp)
            body = ' '.join(block_var(b) for b in blocks_fp)
            out.append('')
            out.append(f'; --- forbid {label} ---')
            out.append(f';   blocks ({n}):  {_fmt_block_list(blocks_fp)}')
            out.append(
                f'(assert ((_ at-most {n - 1}) {body})) ; forbid {label}')

    out.append('(check-sat)')
    out.append('(get-model)')

    smt2 = '\n'.join(out) + '\n'
    return CompletenessProbe(
        smt2=smt2,
        block_vars=tuple(block_var(b) for b in blocks),
        edge_vars=tuple(edge_var(u, v) for u, v in edges),
    )


# ---------------------------- Model → path -----------------------------------


_MODEL_TRUE_RE = re.compile(
    r'\(define-fun\s+(\S+)\s+\(\)\s+Bool\s+(true|false)\s*\)'
)


def parse_true_edge_vars(model_text: str) -> set[tuple[NBId, NBId]]:
    """Parse a z3 `(get-model)` response and return the set of edges
    `(u, v)` whose `e_<u>__TO__<v>` was assigned `true`."""
    out: set[tuple[NBId, NBId]] = set()
    for m in _MODEL_TRUE_RE.finditer(model_text):
        name, val = m.group(1), m.group(2)
        if val != 'true':
            continue
        pair = parse_edge_var(name)
        if pair is not None:
            out.add(pair)
    return out


def derive_path_from_model(info: CfgInfo,
                              model_text: str) -> list[NBId] | None:
    """Walk the model's true edges from entry to assert.

    Per the strategy doc: **do NOT** use `nx.shortest_path` on the
    true-block subgraph — that subgraph may include CFG edges the
    model did NOT pick, and shortest-path takes shortcuts that drop
    blocks the model actually visits, masking real escapes."""
    true_edges = parse_true_edge_vars(model_text)
    if not true_edges:
        return None
    # Index by source block.
    by_src: dict[NBId, list[NBId]] = {}
    for u, v in true_edges:
        by_src.setdefault(u, []).append(v)

    path = [info.entry]
    cur = info.entry
    visited = {info.entry}
    while cur != info.assert_block:
        nxts = by_src.get(cur, [])
        if len(nxts) != 1:
            # Multiple true out-edges or none from `cur` ⇒ model
            # doesn't yield a unique path. The encoding enforces
            # exactly-one, so this only fires on malformed input.
            return None
        nxt = nxts[0]
        if nxt in visited:
            return None
        path.append(nxt)
        visited.add(nxt)
        cur = nxt
        if len(path) > len(by_src) + 1:
            return None  # safety net
    return path
