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
  #text(size: 28pt)[Overview]
]

== Goal

VC generation turns a TAC-like program into an SMT query.

#align(center)[
  $ "sat"("VC"(P, A)) <=> "there exists an execution reaching failure of " A $
]

#v(0.3cm)

*Tiny TAC* (`ttac`) keeps the semantic core visible:

- explicit basic blocks and terminators
- named Boolean branch and assertion conditions
- scalar definitions, havoc, assume, assert
- maps and map updates
- phi nodes at joins

== What The Encoder Consumes

#two-col[
  A `ttac` program gives the VC generator:

  - a control-flow graph
  - commands in each block
  - symbol sorts
  - scalar and map expressions
  - the assertion-failure query
][
  The encoder produces an SMT formula whose models are bug witnesses.

  #logic-box[
    $
      "VC"(P, A) =
        "Path" and
        "Assumes" and
        not "Assert"
    $
  ]

  Unsat means no modeled assertion-failure execution exists.
]

== VCGen Styles

#compact-list[
- *SeaHorn-style*: explicit block reachability variables.
- *Boogie-style*: backward safety equations.
- *SeaBMC-style*: control-dependence compiled into data-dependence.
]

#v(0.35cm)

The encodings differ mainly in how they represent path semantics and joins.

== Running Example Shape

```tac
entry:
  x := havoc
  y := havoc
  c := x < y
  if c goto left else right

left:
  a_left := x + 1
  goto join

right:
  a_right := y + 1
  goto join
```

== Running Example: Join And Exit

```tac
join:
  a := phi [left: a_left, right: a_right]
  ok := a > 0
  goto exit

exit:
  assume true
  assert ok
  halt
```

#v(0.25cm)
This diamond exercises branch conditions, joins, phi nodes, definitions, and
the final failure query.

== Reading The VC

The query orientation is:

#logic-box[
  $
    "SAT" &=> "a bug witness exists" \
    "UNSAT" &=> "the assertion is proved in the modeled semantics"
  $
]

#v(0.35cm)

The main design choice is how to represent path semantics:

- explicit reachability variables
- recursive safety equations
- data-flow gates and ITEs
