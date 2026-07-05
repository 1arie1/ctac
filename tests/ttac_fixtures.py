"""Tiny TAC example programs taken verbatim from ``docs/vc/``.

Not a test module (no ``test_`` prefix) - shared fixtures for the parser
and round-trip tests. Each entry is a complete program.
"""

# docs/vc/sections/syntax-semantics.typ:134-155
CORE = """\
entry:
  M := havoc
  i := havoc
  limit := havoc
  x := M[i]
  y := x + 1
  M2 := M[i := y]
  c := y <= limit
  if c goto ok else bad

ok:
  assert c
  goto exit

bad:
  assume not c
  halt

exit:
  halt
"""

# docs/vc/sections/references-borrowing.typ:92-105
BORROW_SURFACE = """\
entry:
  M := havoc
  i := havoc
  p := borrow M[i]
  x := get_ref p
  release p
  q, M2 := borrow_mut M[i]
  q2 := put_ref q, (x + 1)
  release q2
  ok := M2[i] == x + 1
  assert ok
  halt
"""

# docs/vc/sections/references-borrowing.typ:259-269
MUT_BORROW_SURFACE = """\
entry:
  M := havoc
  i := havoc
  r, M2 := borrow_mut M[i]
  r2 := put_ref r, 7
  release r2
  x := M2[i]
  ok := x == 7
  assert ok
  halt
"""

# docs/vc/sections/references-borrowing.typ:274-286 (lowered form)
MUT_BORROW_LOWERED = """\
entry:
  M := havoc
  i := havoc
  r := { addr: i, value: M[i], promise: havoc }
  M2 := M[i := r.promise]
  r2 := { addr: r.addr, value: 7, promise: r.promise }
  assume r2.value == r2.promise
  x := M2[i]
  ok := x == 7
  assert ok
  halt
"""

# docs/vc/sections/references-borrowing.typ:342-356
REBORROW_SURFACE = """\
entry:
  M := havoc
  i := havoc
  r, M2 := borrow_mut M[i]
  q, r2 := borrow_ref_mut r
  q2 := put_ref q, 7
  release q2
  r3 := put_ref r2, 8
  release r3
  x := M2[i]
  ok := x == 8
  assert ok
  halt
"""

# docs/vc/sections/references-borrowing.typ:361-376 (lowered form)
REBORROW_LOWERED = """\
entry:
  M := havoc
  i := havoc
  r := { addr: i, value: M[i], promise: havoc }
  M2 := M[i := r.promise]
  q := { addr: r.addr, value: r.value, promise: havoc }
  r2 := { addr: r.addr, value: q.promise, promise: r.promise }
  q2 := { addr: q.addr, value: 7, promise: q.promise }
  assume q2.value == q2.promise
  r3 := { addr: r2.addr, value: 8, promise: r2.promise }
  assume r3.value == r3.promise
  x := M2[i]
  ok := x == 8
  assert ok
  halt
"""

# docs/vc/sections/syntax-semantics.typ:179-183
PHI = """\
join:
  x := phi [left: x_left, right: x_right]
  goto exit
"""

# Not from docs/vc - purpose-built for the ttac lean tests.

# docs/vc/examples/safe_scalar_diamond.ttac - scalar-only diamond with
# havoc, phi, branch, and assert; mirrors the golden
# lean/TtacExamples/Diamond.lean pair.
SCALAR_DIAMOND = """\
entry:
  x := havoc
  c := 0 <= x
  if c goto pos else neg

pos:
  y1 := x + 1
  goto join

neg:
  y2 := 0 - x
  goto join

join:
  y := phi [pos: y1, neg: y2]
  ok := 0 <= y
  assert ok
  halt
"""

# Single scalar block: havoc / assign / assume / assert / halt.
SCALAR_STRAIGHT = """\
entry:
  a := havoc
  b := a * 2
  assume 0 <= a
  ok := a <= b
  assert ok
  halt
"""

# docs/vc/examples/safe_bytemap_phi.ttac - stores on both branches, a
# bytemap phi at the join, select + assert; mirrors the golden
# lean/TtacExamples/BytemapVc.lean pair.
BYTEMAP_PHI = """\
entry:
  M := havoc
  i := havoc
  v := havoc
  c := havoc
  if c goto left else right

left:
  M1 := M[i := v]
  goto join

right:
  M2 := M[i := v]
  goto join

join:
  M3 := phi [left: M1, right: M2]
  x := M3[i]
  ok := x == v
  assert ok
  halt
"""

# Not from docs/vc - purpose-built for the ua transform tests.

# Two sequential asserts in one block (merge example).
TWO_ASSERTS = """\
entry:
  a := havoc
  b := havoc
  assert a
  assert b
  halt
"""

# A branch with an assert on each arm (split COI / polarity example).
BRANCH_ASSERTS = """\
entry:
  c := havoc
  x := havoc
  if c goto L else R

L:
  okL := x <= x
  assert okL
  goto exit

R:
  okR := havoc
  assert okR
  goto exit

exit:
  halt
"""

ALL = {
    "CORE": CORE,
    "BORROW_SURFACE": BORROW_SURFACE,
    "MUT_BORROW_SURFACE": MUT_BORROW_SURFACE,
    "MUT_BORROW_LOWERED": MUT_BORROW_LOWERED,
    "REBORROW_SURFACE": REBORROW_SURFACE,
    "REBORROW_LOWERED": REBORROW_LOWERED,
    "PHI": PHI,
}
