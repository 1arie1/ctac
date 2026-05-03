"""TAC transformation passes (CFG-edit primitives, specializers, etc.).

Distinct from :mod:`ctac.rewrite` (which holds local expression
rewrites): transforms here may delete blocks, change CFG topology, or
combine multiple operations into a single user-visible primitive.
"""
