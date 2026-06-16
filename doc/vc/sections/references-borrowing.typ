#import "tac-code.typ": tac-code, logic-box
#show raw.where(lang: "tac"): it => tac-code(it.text)

= References and Borrowing

This section extends Tiny TAC with references. The goal is to model source
languages that distinguish direct map access from access through borrowed
locations, while keeping the VCGen interface explicit.

The extension is intentionally small:

- a reference names a location inside a bytemap,
- a constant reference may be read,
- a mutable reference may be read or written,
- references can be reborrowed from existing references,
- well-formed programs make the lifetime and aliasing obligations explicit
  enough for VC generation.

== Reference Types

Tiny TAC gains reference types:

#align(center)[
  $ tau ::= "bool" | "int" | "bytemap" | "&" tau | "&mut" tau $
]

A value of type $"&" tau$ is a constant reference to a location containing a
$tau$ value. A value of type $"&mut" tau$ is a mutable reference to such a
location.

For the base language in this document, the most important instances are
references to integer cells inside a bytemap:

#align(center)[
  $ r : "&int" quad q : "&mut int" $
]

Symbolically, a reference carries three fields:

- the address to which the reference points,
- the value currently observed through the reference,
- the promised value at that address when the reference is released.

For the lowering below, we represent each reference as a triple:

#align(center)[
  $ r = { "addr": i, "value": v, "promise": p } $
]

The `addr` field is the address to which the reference points. The `value`
field is the value stored at that address from the reference's point of view.
The `promise` field is the value that will be stored at that address when the
reference is released. Constant references do not use their promise field, but
we keep the same triple shape for simplicity.

Tiny TAC does not otherwise have tuples or field projection. In this section,
record literals such as `{ addr: i, value: v, promise: p }` and projections
such as `r.value` are syntactic sugar used only to explain the lowering.

== Borrowing Commands

The command grammar is extended with explicit borrow, reborrow, `get_ref`,
`put_ref`, and release commands:

```text
cmd ::= ...
      | r := borrow M[i]
      | r, M2 := borrow_mut M[i]
      | q := borrow_ref r
      | q, r2 := borrow_ref_mut r
      | x := get_ref r
      | r2 := put_ref r, v
      | release r
```

The first two commands borrow a concrete memory location. The next two commands
reborrow the location described by an existing reference. `get_ref` observes the
value through a reference. `put_ref` updates the value through a mutable
reference and returns a fresh reference value. `release` ends the reference
lifetime for the purposes of well-formedness checking.

A constant borrow returns only the new reference because it cannot modify the
underlying bytemap. A mutable borrow returns the new reference and a
continuation bytemap that records any potential modification through the
borrowed reference. Mutable reborrowing similarly returns the new reference `q`
and a continuation reference `r2` that represents the original reference after
the borrow of `q` ends. This keeps the program in SSA form even when a borrow
may mutate through the borrowed reference.

For example:

```tac
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
```

This program first creates a constant reference for reading, releases it, and
then creates a mutable reference to update the same location.

== Reborrowing

Reborrowing creates a new reference to the same location as an existing
reference. The surface syntax is:

```tac
p := borrow M[i]
p2 := borrow_ref p
x := get_ref p2
release p2
release p
```

A mutable reference can also be reborrowed:

```tac
r, M1 := borrow_mut M[i]
q, q_after := borrow_ref_mut r
q2 := put_ref q, 7
release q2
x := get_ref q_after
ok := x == 7
assert ok
release q_after
```

The well-formedness condition is stronger for mutable reborrows: while `q` is
live, the parent reference `r` is suspended. After the borrowed reference is
released, `q_after` represents the resumed parent reference and can observe the
update performed through `q`.

== Borrow Well-Formedness

Borrowing introduces obligations that are best checked before VC generation.
We expect conditions such as: `get_ref` requires a live reference, `put_ref`
requires a live mutable reference, mutable references are exclusive in the
appropriate sense, and reborrows do not outlive the references from which they
were derived.
This document does not attempt to define the exact borrow discipline.

It is also legal in Tiny TAC to mix direct memory operations with reference
operations:

```tac
r, M1 := borrow_mut M[i]
r2 := put_ref r, 7
M2 := M1[j := 9]
release r2
```

This is analogous to a Rust program that mixes safe references with unsafe raw
accesses. The correct well-formedness conditions for such programs depend on
the chosen reference semantics.

One possible family of rules follows _Stacked Borrows_:
(see, #link("https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md")[stacked-borrows.md]).
The Rust unsafe-code-guidelines notes describe it as a non-normative model and
link to the Stacked Borrows paper and related material. Another possible model
is _Tree Borrows_:
(see #link("https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/tree-borrows.md")[tree-borrows.md]).

The rest of this document treats borrow well-formedness as an external side
condition or as an optional set of additional VC obligations, without choosing
between these models.

== Compiling References Away

We can explain VC generation for references by first compiling Tiny TAC with
references into ordinary Tiny TAC plus the tuple notation introduced above.
After this source-to-source lowering, the existing VCGen only needs to handle
ordinary assignments, map reads, map updates, assumptions, and assertions.

For a constant borrow:

```tac
r := borrow M[i]
```

the lowering is:

```tac
r := { addr: i, value: M[i], promise: havoc }
```

The `promise` field is unused for constant references, but keeping it makes all
references have the same shape.

For a mutable borrow:

```tac
r, M2 := borrow_mut M[i]
```

the lowering is:

```tac
r := { addr: i, value: M[i], promise: havoc }
M2 := M[i := r.promise]
```

The map `M2` is the continuation memory: when `r` is eventually released, the
borrow promises that address `i` contains `r.promise`.

For a `get_ref`:

```tac
x := get_ref r
```

the lowering is:

```tac
x := r.value
```

For a `put_ref` through a mutable reference:

```tac
r2 := put_ref r, v
```

the lowering is:

```tac
r2 := { addr: r.addr, value: v, promise: r.promise }
```

The `put_ref` returns a fresh reference symbol so the lowered program remains in
SSA form.

For a release:

```tac
release r
```

the lowering is:

```tac
assume r.value == r.promise
```

This assumption connects the value observed through the reference at release
time with the promise that was already written into the continuation memory.

=== Example: Direct Mutable Borrow

Consider this Tiny TAC program with references:

```tac
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
```

The reference commands compile to:

```tac
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
```

After substituting the tuple fields, the relevant facts are:

#logic-box[
  $
    "M2" & = M[i := "promise"(r)] \
    "value"("r2") & = 7 \
    "promise"("r2") & = "promise"(r) \
    "value"("r2") & = "promise"("r2")
  $
]

Together these imply $"promise"(r) = 7$, so the continuation memory `M2` stores
`7` at address `i`. The final assertion is therefore the ordinary Tiny TAC fact
that `M2[i] == 7`.

== Compiling Borrowed References

Reborrowing is also compiled away using the same reference triple. A constant
reborrow:

```tac
q := borrow_ref r
```

compiles to:

```tac
q := { addr: r.addr, value: r.value, promise: havoc }
```

The child reference `q` observes the same address and current value as `r`.
Since `q` is constant, its promise is unused.

A mutable reborrow:

```tac
q, r2 := borrow_ref_mut r
```

compiles to:

```tac
q := { addr: r.addr, value: r.value, promise: havoc }
r2 := { addr: r.addr, value: q.promise, promise: r.promise }
```

When `q` is released, it updates the value of `r2`. When `r2` is released, it
updates the value that `r` promised to release. At the same time, `r` is
consumed and converted to `r2`, so `r` itself is never released.

=== Example: Mutable Reborrow

Consider:

```tac
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
```

The reference commands compile to:

```tac
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
```

The first release gives `q.promise == 7`, so `r2.value == 7`. The update through
`r2` then changes the value to `8` while preserving `r.promise` as the final
promise. Releasing `r3` gives `r.promise == 8`, which is the value already
written into the continuation memory `M2`.

The relevant equalities are:

#logic-box[
  $
    "M2" & = M[i := "promise"(r)] \
    "promise"("r2") & = "promise"(r) \
    "value"("q2") & = 7 \
    "promise"("q2") & = "promise"(q) \
    "value"("q2") & = "promise"("q2") \
    "value"("r3") & = 8 \
    "promise"("r3") & = "promise"("r2") \
    "value"("r3") & = "promise"("r3")
  $
]

These imply $"promise"(r) = 8$, so `M2[i] == 8`. The value written by `q` is
visible through `r2`, but the final update through `r2` determines the value
that the original mutable borrow commits to memory.

== VCGen Extension

With this lowering, references do not require a separate VCGen core rule in
the direct-borrow and reborrow cases above. VCGen can first compile reference
commands away, then run the ordinary Tiny TAC encoding on the resulting
program.

== Extensions and Discussion

The `promise` field is an instance of a _prophecy variable_: a nondeterministic
value chosen now and constrained later when the promised event occurs. Prophecy
variables were introduced by Abadi and Lamport in
#link("https://doi.org/10.1016/0304-3975(91)90224-P")[_The Existence of Refinement Mappings_]
in the context of proving refinement between concurrent and reactive system
specifications. Later presentations, such as Lamport and Merz's
#link("https://arxiv.org/abs/1703.05121")[_Auxiliary Variables in TLA+_],
describe prophecy variables together with history and stuttering variables as
auxiliary variables that can be added to a specification without changing its
observable behaviors.

The same idea appears in verification of concurrent data structures and model
checking when a proof needs to refer to a value that will only be determined by
a future step. In the borrow encoding above, the future step is `release`: the
borrow begins by choosing a promised final value, and the release later
fulfills that promise.

The use of prophecy-style values to model Rust borrows is due to RustHorn:
#link("https://arxiv.org/abs/2002.09002")[_RustHorn: CHC-based Verification for Rust Programs_]
by Matsushita, Tsukada, and Kobayashi. RustHorn represents a mutable reference
using the current value and the value at the end of the borrow, avoiding an
explicit memory model for safe Rust-style ownership.

Priya and Gurfinkel adapt this idea to a bounded-model-checking setting in
#link("https://arxiv.org/abs/2408.04043")[_Ownership in low-level intermediate representation_]
(FMCAD 2024). Their setting is lower-level than RustHorn: ownership information
is used opportunistically in an LLVM-like IR, while unsafe or raw-style accesses
may still require synchronization with an address-map memory model.

The Tiny TAC presentation here follows the same broad pattern, but remains only
a small explanatory model. The next questions are how to combine the prophecy
translation with the chosen borrow well-formedness discipline, how to handle
mixed direct-memory and reference accesses, and how much of the resulting
translation should be treated as preprocessing versus part of VCGen proper.

Several extensions are left open. Each is small enough to state independently,
but substantial enough to be a useful project.

- *Finite-region borrows.* The examples restrict memory borrows to a single
  memory cell. A natural extension is to borrow an arbitrary finite region,
  such as a collection of bytes. The reference representation would then need
  to describe a base address, a size or set of offsets, and a value/promise for
  each byte or word in the region. The main question is how to keep the
  resulting encoding compact while still allowing accesses inside the borrowed
  region to use the reference representation instead of the full memory map.

- *Reference shadow memory.* Tiny TAC does not allow references to be stored in
  memory, because a reference triple does not fit into a single `int`. One way
  to model stored references is to add ghostmaps for shadow memory. For every
  ordinary memory byte, the encoding could maintain corresponding shadow values
  that store reference metadata such as address, value, promise, permission, or
  validity. The design question is which metadata must be shadowed, and how
  shadow updates stay synchronized with ordinary memory updates.

- *Reference semantics and well-formedness.* This section has not given a
  precise semantics for references, especially when reference operations are
  mixed with raw memory accesses. It also has not specified how to check borrow
  well-formedness. A project in this direction could choose a model, such as a
  Stacked Borrows or Tree Borrows variant, state the well-formedness rules, and
  decide whether violations are rejected before VCGen or encoded as additional
  verification obligations.
