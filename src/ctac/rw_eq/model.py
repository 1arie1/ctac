"""Result dataclasses for the rewriter equivalence checker."""

from __future__ import annotations

from dataclasses import dataclass

from ctac.ir.models import NBId, TacBlock, TacProgram


@dataclass(frozen=True)
class BlockRef:
    """Typed reference to a TAC block.

    Wraps ``NBId`` so block-identifier-typed APIs in the rw-eq
    stuttering-simulation modules are distinct from raw strings
    (symbol names, cmd text, ...). Scope is intentionally local to
    the new stutter-mode code; existing ctac call sites continue to
    use bare ``NBId`` / ``str`` (see ``feedback_ast_type_refactor_scope``
    in user memory for why the global refactor is out of scope).
    """

    id: NBId

    def __str__(self) -> str:
        return self.id

    @classmethod
    def of(cls, block: TacBlock) -> "BlockRef":
        return cls(id=block.id)


@dataclass(frozen=True)
class RehavocSite:
    """One occurrence of rule 6 (rehavoc) firing.

    ``block_id`` and ``cmd_index`` point at the LHS's ``X = e``
    command position; ``var_name`` is X (the rehavoc'd LHS symbol);
    ``shadow_name`` is the fresh ``X_new`` we minted.
    """

    block_id: str
    cmd_index: int
    var_name: str
    shadow_name: str


@dataclass(frozen=True)
class EquivResult:
    """Outcome of :func:`emit_equivalence_program`.

    ``program`` is the merged TAC program. ``rule_hits`` counts each
    rule's firings. ``rehavoc_sites`` lists every rule-6 admission for
    the loud-warning report. ``extra_symbols`` lists all symbols added
    to the merged program's symbol table (CHK<n> bools, rehavoc
    shadows, DEST_A / IN_DEST_B ints when in stuttering-simulation
    mode).

    Stutter-mode fields are empty tuples for the (default) lockstep
    path; populated when the walker engages the stuttering branch.
    """

    program: TacProgram
    rule_hits: dict[str, int]
    rehavoc_sites: tuple[RehavocSite, ...] = ()
    extra_symbols: tuple[tuple[str, str], ...] = ()
    asserts_emitted: int = 0
    feasibility_asserts_emitted: int = 0
    stutter_blocks: tuple[BlockRef, ...] = ()
    divergence_points: tuple[BlockRef, ...] = ()
    sync_points: tuple[BlockRef, ...] = ()


class EquivContractError(ValueError):
    """Raised when the (orig, rw) pair violates the rw-eq input contract:
    different block ids, different successors, terminator mismatch, or
    a lockstep step that none of the matching rules accepts."""


class StructuralSimError(EquivContractError):
    """Raised when a stuttering-mode (orig, rw) pair fails the structural
    pre-check.

    Two distinct failure modes carry their own diagnostic shape:

    - **Joint-post-dominator violation.** From some divergence point A,
      LHS τ-paths reach a frontier that is not exactly RHS's target
      set ``T``. The simulation relation is not well-defined.
    - **Shared stutter region.** Two divergence points A1, A2 both
      reach some stutter block s through their τ-regions; the per-A
      ``DEST_A`` picker would be ambiguous. The current cleanup scope
      (single-pred-single-succ stutter chains) doesn't exercise this
      shape; if a future rewriter pass does, the choice is either
      full SSA at dominance frontiers or revert to single-global DEST.
    """
