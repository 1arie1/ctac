#import "@preview/touying:0.7.4": *
#import themes.simple: *
#import "common.typ": *

#show: simple-theme.with(
  aspect-ratio: "16-9",
  config-common(horizontal-line-to-pagebreak: false),
)
#show raw.where(lang: "tac"): it => tac-code(
  it.text,
  font: "Consolas for Powerline",
  font-size: 12pt,
  inset: (x: 9pt, y: 7pt),
)
#set text(font: "Verdana", size: 18pt)
#set par(justify: false)

#let smt-box(s) = block(
  fill: rgb("#f8fafc"),
  stroke: 0.6pt + rgb("#dbe3ee"),
  radius: 3pt,
  inset: (x: 10pt, y: 8pt),
  width: 100%,
)[
  #set text(font: "Menlo", size: 12pt)
  #set par(leading: 0.42em)
  #raw(s)
]

#title-slide[
  #text(size: 44pt, weight: "bold")[VC Generation]
  #v(0.2cm)
  #text(size: 28pt)[Overview]
  #v(0.8cm)
  #text(size: 18pt, weight: "medium", fill: muted)[Crafted by Arie Gurfinkel]
  #linebreak()
  #text(size: 16pt, fill: muted)[Made by Codex 🤖]
  #linebreak()
  #text(size: 14pt, fill: accent)[
    #link("https://github.com/1arie1/ctac")[github.com/1arie1/ctac]
  ]
  #v(0.7cm)
  #image("assets/waterloo-engineering-logo-horiz-rgb.png", width: 8.6cm)
]

== Is This Program Safe?

#two-col[
  ```tac
  entry:
    M := havoc
    i := havoc
    x := M[i]
    ok := x == 0
    assert ok
    halt
  ```
][
  #question-box[
    Can `assert ok` fail?

    If so: which values of `M` and `i` break it?
  ]

  #pause
  #v(0.3cm)

  #term-box[
    #sh[ttac vcgen unsafe_bytemap.ttac --solve]
    #hi[sat]
  ]

  #v(0.15cm)
  #sat-chip #h(0.4em) a failing execution exists.
]

== The Counterexample, Replayed

The solver returns a *model* — concrete values for every symbol:

#term-box[
  #sh[ttac vcgen unsafe_bytemap.ttac --solve --model m.txt]
  #hi[sat]
  #out[i = 1 #h(2em) x = 2 #h(2em) ok = false #h(2em) M = (lambda addr. 2)]
]

#pause
#v(0.3cm)

The interpreter replays the model into the failing assert:

#term-box[
  #sh[ttac run unsafe_bytemap.ttac --model m.txt]
  #hi[status: assert_failed (assertion failed in block entry)]
  #out[steps: 5 #h(2em) assert_ok: 0 #h(2em) assert_fail: 1]
]

== What Did The Solver Actually See?

#two-col(columns: (1.15fr, 1fr))[
  #smt-box("(set-logic QF_UFNIA)

(declare-const i Int)
(declare-const x Int)
(declare-const ok Bool)
(declare-const BLK_EXIT Bool)
(declare-fun M (Int) Int)

; block entry
(assert (= x (M i)))
(assert (= ok (= x 0)))

; cfg constraints
(assert (=> BLK_EXIT (not ok)))
(assert BLK_EXIT)

(check-sat)")
][
  Not the program — this formula: the *verification condition* (VC).

  #v(0.2cm)

  - assignments became equalities
  - the assert became its negation
  - control flow became constraints

  #v(0.2cm)

  *VC generation* is the translation. These lectures are about how it works —
  and how it goes wrong.
]

== The Contract

VC generation turns a TAC-like program into an SMT query:

#align(center)[
  $ "sat"("VC"(P, A)) <=> "there exists an execution reaching failure of " A $
]

#v(0.3cm)

#logic-box[
  $
    "SAT" &=> "a bug witness exists — the model is the failing execution" \
    "UNSAT" &=> "the assertion is proved in the modeled semantics"
  $
]

#v(0.3cm)

*Tiny TAC* (`ttac`) keeps the semantic core visible: basic blocks and
terminators, named branch and assert conditions, havoc, assume,
maps, and phi nodes at joins.

== The Running Example

One diamond carries the whole lecture series — branches, a join, a phi
node, definitions, and a final failure query:

#v(0.2cm)
#diamond-cfg-full(t-label: $c$, f-label: $not c$)

#v(0.3cm)
Every encoder in this series processes *this* graph.

== Three Encodings of the Same Graph

#compact-list[
- *SeaHorn-style* — control flow stays explicit: one reachability
  variable per block, constrained to describe a path.
- *Boogie-style* — control flow becomes recursion: one backward safety
  equation per block.
- *SeaBMC-style* — control flow disappears: control-dependence is
  compiled into data-dependence, then the VC is a flat conjunction.
]

#v(0.3cm)

The encodings differ only in how they represent *path semantics* —
definitions, assumes, and the failure query look alike in all three.

#v(0.3cm)

#text(fill: muted, size: 16pt)[
  Series: 01 Tiny TAC · 02 well-formedness · 03 SeaHorn · 04 Boogie ·
  05 SeaBMC + comparison · 06 references and borrowing
]
