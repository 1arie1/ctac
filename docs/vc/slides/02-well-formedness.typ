#import "@preview/touying:0.7.4": *
#import themes.simple: *
#import "common.typ": *

#show: simple-theme.with(aspect-ratio: "16-9")
#show raw.where(lang: "tac"): it => tac-code(
  it.text,
  font: "Consolas for Powerline",
  font-size: 12pt,
  inset: (x: 9pt, y: 7pt),
)
#set text(font: "Verdana", size: 18pt)
#set par(justify: false)

#title-slide[
  #text(size: 44pt, weight: "bold")[VC Generation]
  #v(0.2cm)
  #text(size: 28pt)[Well-Formed Programs]
]

== Why Preconditions Exist

The grammar accepts more programs than the encoders should consume.

#v(0.3cm)

Well-formedness records the shape expected by each VCGen style:

- CFG shape: entry, exit, paths
- definition discipline: SSA or DSA
- assertion discipline: single final failure query
- join discipline: phi nodes or edge-local dynamic definitions

== CFG Vocabulary

#two-col[
  A CFG has:

  - one node per basic block
  - edge `b -> b'` when `b` can transfer to `b'`
  - successors from outgoing edges
  - predecessors from incoming edges
][
  ```tac
  entry:
    c := havoc
    if c goto left else right

  left:
    goto join

  right:
    goto join
  ```
]

== SESE

A program is *single-entry single-exit* when:

- `entry` and `exit` are distinguished and distinct
- execution starts only at `entry`
- normal completed executions end at `exit`
- every block lies on an entry-to-exit path

#v(0.35cm)
#logic-box[
  $
    "SESE" = "no unreachable blocks, no dead regions, one normal exit"
  $
]

== SSA

Static single assignment:

- every register is assigned at most once
- phi assignments are a prefix of the join block
- every phi has one incoming value per predecessor

```tac
left:
  x_left := 1
  goto join

right:
  x_right := 2
  goto join

join:
  x := phi [left: x_left, right: x_right]
```

== DSA

Dynamic single assignment pushes the merge onto incoming edges.

```tac
left:
  x_left := 1
  x := x_left
  goto join

right:
  x_right := 2
  x := x_right
  goto join

join:
  goto exit
```

The two assignments to `x` are allowed because they occur in sibling
predecessors, immediately before the join.

== SSA To DSA

#two-col[
  Before:

  ```tac
  join:
    x := phi [p1: v1, p2: v2]
    goto exit
  ```
][
  After:

  ```tac
  p1:
    x := v1
    goto join

  p2:
    x := v2
    goto join
  ```
]

#v(0.2cm)
DSA can be read as placing the merge assignment on the incoming CFG edge.

== SASA

Single-assume single-assert form puts the query at the exit:

```tac
exit:
  assume pre
  assert post
  halt
```

#v(0.25cm)

- exactly one `assume`
- exactly one `assert`
- `pre` accumulates path assumptions
- `post` summarizes assertion obligations

== Safety Query

For a SASA program, safety is:

#align(center)[
  $ forall xi. "entry-to-exit"(xi) => ("pre"(xi) => "post"(xi)) $
]

The VC asks for the negation:

#align(center)[
  $ exists xi. "entry-to-exit"(xi) and "pre"(xi) and not "post"(xi) $
]
