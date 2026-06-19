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
  #text(size: 28pt)[SeaHorn Style]
]

== Idea

SeaHorn-style VCGen keeps control flow explicit.

#v(0.2cm)

For each block `i`, introduce a Boolean reachability variable:

#align(center)[
  $ bb_i $
]

Then constrain the selected blocks so they describe an entry-to-exit path.

== Formula Shape

#logic-box[
  $
    "VCGen_SeaHorn"(P) =
      #formula-part[CFG] and
      #formula-part[DEF] and
      #formula-part[JUMPS] and
      #formula-part[PHI] and
      #formula-part[ERROR]
  $
]

#compact-list[
- `CFG`: selected block variables form a path.
- `DEF`: assignments hold when their block is selected.
- `JUMPS`: selected branch edges satisfy branch conditions.
- `PHI`: selected incoming edges choose phi values.
- `ERROR`: the selected exit violates the assertion.
]

== CFG Constraints

#logic-box[
  $
    #formula-part[CFG] =
      bb_"entry" \
      and forall i != "entry". bb_i => or_(j in "pred"(i)) bb_j \
      and bb_"exit"
  $
]

#v(0.25cm)

Concrete encoders may add edge variables, forward constraints, dominator
constraints, or at-most-one constraints. The semantic role is the same:
describe feasible control.

== Running Diamond

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

== Join And Error

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

== Encoded Pieces

#logic-box[
  $
    #formula-part[DEF] &=
      (bb_"entry" => c = (x < y)) \
      &quad and (bb_"left" => a_"left" = x + 1) \
      &quad and (bb_"right" => a_"right" = y + 1) \
      &quad and (bb_"join" => "ok" = (a > 0)) \
    #formula-part[JUMPS] &=
      ((bb_"entry" and bb_"left") => c) \
      &quad and ((bb_"entry" and bb_"right") => not c) \
    #formula-part[PHI] &=
      ((bb_"left" and bb_"join") => a = a_"left") \
      &quad and ((bb_"right" and bb_"join") => a = a_"right")
  $
]

== Error Condition

For the SASA exit block:

```tac
exit:
  assume pre
  assert post
  halt
```

emit:

#logic-box[
  $
    #formula-part[ERROR] = bb_"exit" => "pre" and not "post"
  $
]

Together with `bb_exit`, this asks for a complete failing execution.

== Optimization: Unguarded DEF

Static definitions may be exposed as top-level equations:

#two-col[
  Guarded:

  #logic-box[
    $ bb_i => x = y + 1 $
  ]
][
  Unguarded:

  #logic-box[
    $ x = y + 1 $
  ]
]

The unguarded form helps substitution and algebraic simplification, but only
when the definition and its side conditions are globally safe.

== Optimization: Phi As ITE

#two-col[
  Edge implications:

  #logic-box[
    $
      (bb_i and bb_j) => x = x_i \
      (bb_k and bb_j) => x = x_k
    $
  ]
][
  One defining equation:

  #logic-box[
    $ x = "ite"(bb_i, x_i, x_k) $
  ]
]

After Boolean propagation learns `bb_i`, the ITE collapses to `x = x_i`.

== Pitfall: Critical Edges

An edge `u -> v` is critical when:

#align(center)[
  $ |"succ"(u)| > 1 and |"pred"(v)| > 1 $
]

#align(center)[#image("../sections/critical-edge.svg", width: 72%)]

Block variables alone do not identify which incoming edge was taken.

== Critical Edge Example

```tac
entry:
  c := havoc
  if c goto join else mid

mid:
  goto join

join:
  ok := phi [entry: true, mid: false]
```

Bad true-edge encoding:

#logic-box[
  $ (bb_"entry" and bb_"join") => c $
]

On path `entry -> mid -> join`, both blocks are selected while `c` is false.
The real bug path can be incorrectly rejected.

== Pitfall: ITE Merge Exclusivity

If both predecessors can be selected, independent ITE merges can create a mixed
state:

#logic-box[
  $
    x = "ite"(bb_"left", x_"left", x_"right") \
    p = "ite"(bb_"right", p_"right", p_"left")
  $
]

Repair:

#logic-box[
  $ not (bb_"left" and bb_"right") $
]

At most one incoming predecessor may feed a merge.
