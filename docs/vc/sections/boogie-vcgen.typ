#import "tac-code.typ": tac-code, logic-box
#show raw.where(lang: "tac"): it => tac-code(it.text)
#let formula-part(body) = text(fill: rgb("#0369a1"), weight: "semibold")[#body]

== Boogie-Style VCGen

The Boogie-style VC generator interprets verification as a structured
weakest-precondition computation over a CFG. We present a simplified variant
tailored to loop-free programs in DSA form.

For this section, assume:

- the input program is in DSA form;
- there are no phi nodes;
- dynamic DSA definitions that depend on the predecessor edge are attached to
  that edge.

For each basic block $i$, introduce a Boolean variable $"ok"_i$. Intuitively,
$"ok"_i$ means: starting execution at block $i$ is safe. The final verification
condition asks for a counterexample by requiring the entry block not to be
safe:

#math.equation(block: true, numbering: "(1)", $
  not "ok"_"entry"
$) <eq:boogie-discharge>

=== Block Equations

For each block $i$, define $"ok"_i$ by one equation. Let:

- $"defs"_i$ be the conjunction of the static definitions and assumptions in
  block $i$;
- $"asserts"_i$ be the conjunction of the assertion predicates in block $i$,
  or $top$ if the block has no assertions;
- $"cond"_(i,j)$ be the edge condition for edge $i -> j$; for an
  unconditional edge, $"cond"_(i,j) = top$;
- $"dsa"_(i,j)$ be the conjunction of DSA edge definitions for edge $i -> j$,
  or $top$ if the edge has no such definitions.

Then:

#math.equation(block: true, numbering: "(1)", $
  "ok"_i <=> (
    "defs"_i =>
      (
        "asserts"_i
        and
        and_(j in "succ"(i)) (
          ("cond"_(i,j) and "dsa"_(i,j)) => "ok"_j
        )
      )
  )
$) <eq:boogie-ok>

For a terminal block, the successor conjunction is $top$, so the equation
reduces to:

#math.equation(block: true, numbering: "(1)", $
  "ok"_i <=> ("defs"_i => "asserts"_i)
$) <eq:boogie-terminal>

The shape is backward: a block is safe when its local facts imply that every
feasible successor state is safe. Assumptions appear on the left of the
implication, so an infeasible block is safe vacuously. Assertions appear on the
right, so a reachable false assertion makes the corresponding $"ok"_i$ false.

Havoc assignments do not contribute equalities to $"defs"_i$; they leave their
destination variables unconstrained. Static assignments contribute ordinary
equalities. Edge-sensitive DSA definitions contribute to $"dsa"_(i,j)$.

=== Example 1: Basic Diamond Encoding

Consider the diamond from Example 1, written in pure DSA form by attaching the
merge assignment for `a` to the incoming edges of `join`:

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

join:
  ok := a > 0
  goto exit

exit:
  assume true
  assert ok
  halt
```

The DSA edge definitions are:

#logic-box[
  $
    "dsa"_("left","join") &= (a = a_"left") \
    "dsa"_("right","join") &= (a = a_"right")
  $
]

The Boogie-style VC is:

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
      ) \
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

The model of the VC chooses values for the havoc variables and for the
edge-defined merge variable $a$. The equation for `entry` says that the unsafe
witness must follow a branch whose successor is unsafe; the equations for
`left` and `right` add the corresponding DSA edge definition before checking
`join`.

=== Example 2: Optimized Diamond Encoding

Using the optimized diamond from Example 2, the merge can instead be represented
as a static ITE at `join`:

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

join:
  a := ite(c, a_left, a_right)
  ok := a > 0
  goto exit

exit:
  assume true
  assert ok
  halt
```

Now there are no edge definitions for `join`; the merge is part of
$"defs"_"join"$:

#logic-box[
  $
    #formula-part[OK]_"entry" &:
      "ok"_"entry" <=> (
        c = (x < y) =>
          ((c => "ok"_"left") and (not c => "ok"_"right"))
      ) \
    #formula-part[OK]_"left" &:
      "ok"_"left" <=> (
        a_"left" = x + 1 => "ok"_"join"
      ) \
    #formula-part[OK]_"right" &:
      "ok"_"right" <=> (
        a_"right" = y + 1 => "ok"_"join"
      ) \
    #formula-part[OK]_"join" &:
      "ok"_"join" <=> (
        (
          a = "ite"(c, a_"left", a_"right")
          and "ok" = (a > 0)
        ) => "ok"_"exit"
      ) \
    #formula-part[OK]_"exit" &:
      "ok"_"exit" <=> "ok" \
    #formula-part[DISCHARGE] &:
      not "ok"_"entry"
  $
]

This version has the same backward shape, but the predecessor-sensitive merge
has been compiled into the local definition of `a` at `join`.

=== Tradeoffs

Advantages:

- No special CFG constraints are needed. The CFG structure is compiled into the
  recursive $"ok"_i$ equations.
- Arbitrarily many assertions are easy to support. Each assertion contributes
  another local consequent to its block equation.

Disadvantages:

- The formula is structurally more complex than a flat path formula.
- Cross-block simplification is harder, because facts are nested under the
  block equations rather than exposed as top-level constraints.

=== Extension

This style of encoding can also support a mixture of phi nodes and DSA
assignments. The DSA assignments remain part of the local block premises or
dynamic edge premises, while phi assignments are compiled into static
definitions using ITE expressions over basic-block variables.

In this extension, the Boogie-style block equations are combined with ordinary
CFG constraints. The CFG variables serve two purposes:

- they define the reachability terms used in the phi ITEs;
- they enforce predecessor exclusivity at merge blocks.

The exclusivity condition is important. If a phi node is encoded as:

#logic-box[
  $
    #formula-part[PHI]_"a" &:
      a = "ite"(bb_"left", a_"left", a_"right")
  $
]

then the formula must ensure that at most one incoming predecessor feeding the
ITE is selected. Otherwise, two predecessor blocks can be true at once and the
ITE will silently choose one arm, creating a mixed state that does not
correspond to any real execution.

This requires:

- no critical edges, so predecessor block variables identify incoming edges to
  the merge;
- exclusivity constraints such as $not (bb_"left" and bb_"right")$ for the
  predecessors of a phi merge.

For the running diamond:

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

join:
  a := phi [left: a_left, right: a_right]
  ok := a > 0
  goto exit

exit:
  assume true
  assert ok
  halt
```

the phi node can be compiled into:

#logic-box[
  $
    #formula-part[PHI]_"a" &:
      a = "ite"(bb_"left", a_"left", a_"right")
  $
]

and the CFG side conditions include:

#logic-box[
  $
    #formula-part[CFG]_"entry" &: bb_"entry" \
    #formula-part[CFG]_"left" &: bb_"left" => bb_"entry" and c \
    #formula-part[CFG]_"right" &: bb_"right" => bb_"entry" and not c \
    #formula-part[CFG]_"join" &: bb_"join" => bb_"left" or bb_"right" \
    #formula-part[CFG]_"excl" &: not (bb_"left" and bb_"right")
  $
]

The corresponding block equations keep the same backward shape:

#logic-box[
  $
    #formula-part[OK]_"entry" &:
      "ok"_"entry" <=> (
        c = (x < y) =>
          ((c => "ok"_"left") and (not c => "ok"_"right"))
      ) \
    #formula-part[OK]_"left" &:
      "ok"_"left" <=> (
        a_"left" = x + 1 => "ok"_"join"
      ) \
    #formula-part[OK]_"right" &:
      "ok"_"right" <=> (
        a_"right" = y + 1 => "ok"_"join"
      ) \
    #formula-part[OK]_"join" &:
      "ok"_"join" <=> (
        (
          a = "ite"(bb_"left", a_"left", a_"right")
          and "ok" = (a > 0)
        ) => "ok"_"exit"
      ) \
    #formula-part[OK]_"exit" &:
      "ok"_"exit" <=> "ok" \
    #formula-part[DISCHARGE] &:
      not "ok"_"entry"
  $
]

The extra CFG constraints are not used to select a path directly in the
Boogie-style recurrence; they make the block variables used by phi ITEs
consistent enough that the ITE definitions denote a single incoming edge.
