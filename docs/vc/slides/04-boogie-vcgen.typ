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

#title-slide[
  #text(size: 44pt, weight: "bold")[VCGen]
  #v(0.2cm)
  #text(size: 28pt)[Boogie Style]
]

== Idea

Boogie-style VCGen uses backward safety equations over the CFG.

#v(0.25cm)

For each block `i`, introduce:

#align(center)[
  $ "ok"_i $
]

`ok_i` means: starting execution at block `i` is safe.

The counterexample query is:

#align(center)[
  $ not "ok"_"entry" $
]

#v(0.2cm)
#text(fill: muted, size: 16pt)[No path selection, no block-reachability
variables — control flow becomes recursion.]

== Block Equation

#logic-box[
  $
    "ok"_i <=> (
      "defs"_i =>
        (
          "asserts"_i
          and
          and_(j in "succ"(i))
            (("cond"_(i,j) and "dsa"_(i,j)) => "ok"_j)
        )
    )
  $
]

#compact-list[
- assumptions and definitions are premises
- assertions are consequents
- each feasible successor must be safe
- infeasible blocks are safe vacuously
]

== Terminal Block

For a terminal block, the successor conjunction is `true`:

#logic-box[
  $
    "ok"_i <=> ("defs"_i => "asserts"_i)
  $
]

#v(0.3cm)

A false reachable assertion makes the local `ok_i` false, then unsafety
propagates backward to `entry`.

== The Diamond, In DSA Form

Boogie-style consumes DSA: the merge moves onto the incoming edges.

#diamond-cfg-full(
  phi-style: "dsa",
  t-label: $c$, f-label: $not c$,
  lj-label: $"dsa": a = a_"left"$,
  rj-label: $"dsa": a = a_"right"$,
)

#v(0.2cm)
The assignments to `a` are *edge-sensitive DSA definitions* — they
enter the formula on the edge premises, not as block facts.

== Encoded Equations

#logic-box[
  $
    #formula-part[OK]_"entry" &:
      "ok"_"entry" <=> (
        c = (x < y) =>
          ((c => "ok"_"left") and (not c => "ok"_"right"))
      ) \
    #formula-part[OK]_"left" &:
      "ok"_"left" <=> (
        a_"left" = x + 1 =>
          ((a = a_"left") => "ok"_"join")
      ) \
    #formula-part[OK]_"right" &:
      "ok"_"right" <=> (
        a_"right" = y + 1 =>
          ((a = a_"right") => "ok"_"join")
      )
  $
]

== Encoded Exit

#logic-box[
  $
    #formula-part[OK]_"join" &:
      "ok"_"join" <=> (
        "ok" = (a > 0) => "ok"_"exit"
      ) \
    #formula-part[OK]_"exit" &:
      "ok"_"exit" <=> "ok" \
    #formula-part[DISCHARGE] &:
      not "ok"_"entry"
  $
]

The model chooses havoc values and a branch whose successor is unsafe.

== A Model, Walked Backward

The diamond is unsafe ($a$ can be $<= 0$). Watch the solver's model
flow through the equations:

#compact-list[
- model picks $x = -2, quad y = 0, quad a = a_"left" = -1, quad "ok" = "false"$
#pause
- $"OK"_"exit"$: $"ok"_"exit" <=> "ok"$, so $"ok"_"exit" = "false"$
#pause
- $"OK"_"join"$: premise $"ok" = (a > 0)$ holds ($-1 > 0$ is false), successor
  unsafe #sym.arrow.r $"ok"_"join" = "false"$
#pause
- $"OK"_"left"$: premises $a_"left" = x + 1 = -1$ and edge definition
  $a = a_"left"$ hold #sym.arrow.r $"ok"_"left" = "false"$
#pause
- $"OK"_"entry"$: $c = (x < y) = "true"$, and the true branch requires
  $c => "ok"_"left"$ #sym.arrow.r $"ok"_"entry" = "false"$
#pause
- #formula-part[DISCHARGE] $not "ok"_"entry"$ is satisfied — the model *is*
  the failing execution `entry -> left -> join -> exit`.
]

== Static ITE Merge Variant

The merge can be compiled into an ordinary definition:

```tac
join:
  a := ite(c, a_left, a_right)
  ok := a > 0
  goto exit
```

#logic-box[
  $
    "ok"_"join" <=> (
      (
        a = "ite"(c, a_"left", a_"right")
        and "ok" = (a > 0)
      ) => "ok"_"exit"
    )
  $
]

Now `left` and `right` have no edge definitions — the
predecessor-sensitive merge became a local fact of `join`.

== Tradeoffs

#two-col[
  Advantages:

  - no separate path-selection formula
  - many assertions are natural
  - assumptions are handled by implication
][
  Costs:

  - formula is nested
  - cross-block simplification is harder
  - phi/ITE extensions need exclusivity side conditions
]

== Phi Extension Needs CFG Facts

If a phi is compiled as:

#logic-box[
  $ a = "ite"(bb_"left", a_"left", a_"right") $
]

then the block variables used by the ITE must be consistent:

#logic-box[
  $
    bb_"join" => bb_"left" or bb_"right" \
    not (bb_"left" and bb_"right")
  $
]

The backward equations prove safety; the CFG facts keep the ITE merge
faithful — the same exclusivity pitfall as SeaHorn's phi-as-ITE.

== Same Diamond, Two Formulas

#two-col[
  *SeaHorn* — flat conjunction:

  #logic-box[
    #set text(size: 13.5pt)
    $
      bb_"entry" and bb_"exit" and dots \
      bb_"entry" => c = (x < y) \
      bb_"left" => a_"left" = x + 1 \
      (bb_"entry" and bb_"left") => c \
      (bb_"left" and bb_"join") => a = a_"left" \
      bb_"exit" => not "ok"
    $
  ]

  facts at top level; path selected by block variables
][
  *Boogie* — nested recursion:

  #logic-box[
    #set text(size: 13.5pt)
    $
      not "ok"_"entry" \
      "ok"_"entry" <=> (c = (x < y) => \
        quad ((c => "ok"_"left") and (not c => "ok"_"right"))) \
      "ok"_"left" <=> (a_"left" = x + 1 => \
        quad ((a = a_"left") => "ok"_"join")) \
      dots
    $
  ]

  facts nested under equations; path selected by implication chains
]

#v(0.25cm)
Same models, same verdict — different levers for the solver: SeaHorn
exposes equalities for substitution; Boogie gets assertions and
assumptions for free.
