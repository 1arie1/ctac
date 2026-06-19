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

== DSA Diamond

```tac
entry:
  x := havoc
  y := havoc
  c := x < y
  if c goto left else right

left:
  a_left := x + 1
  a := a_left
  goto join

right:
  a_right := y + 1
  a := a_right
  goto join
```

== DSA Diamond: Exit

```tac
join:
  ok := a > 0
  goto exit

exit:
  assume true
  assert ok
  halt
```

The assignments to `a` are edge-sensitive DSA definitions for the incoming
edges to `join`.

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

The backward equations prove safety; the CFG facts keep the ITE merge faithful.
