#import "tac-code.typ": tac-code, logic-box
#show raw.where(lang: "tac"): it => tac-code(it.text)
#let formula-part(body) = text(fill: rgb("#0369a1"), weight: "semibold")[#body]

== SeaHorn-Style VC Generation

$"VCGen_SeaHorn"$ keeps control flow explicit by introducing one Boolean variable per basic
block, then constraining those variables so they describe an entry-to-exit
path.

=== Basics

The generated formula has the shape:

#math.equation(block: true, numbering: "(1)", $
  "VCGen_SeaHorn"(P)
    = "CFG" and "DEF" and "JUMPS" and "PHI" and "ERROR"
$) <eq:seahorn-shape>

Each conjunct has a separate role:

- `CFG` selects a feasible path through the control-flow graph.
- `DEF` gives semantics to static assignments.
- `JUMPS` enforces branch conditions on selected control-flow edges.
- `PHI` gives semantics to phi assignments at joins.
- `ERROR` requires the selected path to violate the final assertion.

==== CFG

For each basic block $i in "BB"(P)$, introduce a Boolean block variable: $"bb"_i$.


The CFG constraints require the entry block, require the exit block, and require
every selected non-entry block to have a selected predecessor:

#math.equation(block: true, numbering: "(1)", $
  "CFG" =
    &bb_"entry" \
    &and forall i != "entry". bb_i => or_(j in "pred"(i)) bb_j \
    &and bb_"exit"
$) <eq:seahorn-cfg>

The middle constraint is generated for each non-entry block $i$. Concrete
encodings may add equivalent strengthening constraints, such as edge variables
or at-most-one constraints, but the basic purpose is the same: the selected
block variables describe a path from $"entry"$ to $"exit"$.

==== DEF

Static assignments are guarded by the block in which they appear. For a block
$i$, collect its static assignments:

```tac
x1 := e1
x2 := e2
...
xk := ek
```

and emit:

#math.equation(block: true, numbering: "(1)", $
  "DEF"_i = bb_i => and_(m = 1)^k (x_m = e_m)
$) <eq:seahorn-def>

Assignments become equalities in the formula. Havoc assignments do not produce
a defining equality; they leave the assigned variable unconstrained except for
its type.

==== JUMPS

Branch conditions are enforced only when the corresponding edge is selected.
For a conditional terminator:

```tac
if c goto t else f
```

the selected true edge implies $c$, and the selected false edge implies
$not c$:

#math.equation(block: true, numbering: "(1)", $
  "JUMPS"_(i,t) &= (bb_i and bb_t) => c \
  "JUMPS"_(i,f) &= (bb_i and bb_f) => not c
$) <eq:seahorn-jumps>

Unconditional edges have no additional jump condition.

==== PHI

Phi assignments are also edge-sensitive. If block $j$ starts with:

```tac
x := phi [i: x_i, k: x_k]
```

then selecting edge $i -> j$ selects the corresponding incoming value:

#math.equation(block: true, numbering: "(1)", $
  "PHI"_(i,j) &= (bb_i and bb_j) => x = x_i \
  "PHI"_(k,j) &= (bb_k and bb_j) => x = x_k
$) <eq:seahorn-phi>

This is the SSA version of the DSA idea that dynamic assignments live on
predecessor edges.

==== ERROR

For a SASA exit block:

```tac
exit:
  assume pre
  assert post
  halt
```

the error condition requires the selected exit state to satisfy `pre` and
falsify `post`:

#math.equation(block: true, numbering: "(1)", $
  "ERROR" = bb_"exit" => "pre" and not "post"
$) <eq:seahorn-error>

Together with the explicit constraint $bb_"exit"$, this asks for a complete
entry-to-exit execution that reaches the assertion failure condition.

==== Example 1: Basic Diamond Encoding

Consider:

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

The $"VCGen_SeaHorn"$ formula contains:

#logic-box[
  $
    #formula-part[CFG] &= bb_"entry" \
      &quad and (bb_"left" => bb_"entry") \
      &quad and (bb_"right" => bb_"entry") \
      &quad and (bb_"join" => bb_"left" or bb_"right") \
      &quad and (bb_"exit" => bb_"join") \
      &quad and bb_"exit" \
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
      &quad and ((bb_"right" and bb_"join") => a = a_"right") \
    #formula-part[ERROR] &= bb_"exit" => top and not "ok"
  $
]

The satisfying models of this formula are precisely candidate unsafe
executions: selected blocks form an entry-to-exit path, assignments and edge
conditions agree with that path, and the exit assertion is false.

=== Optimizations

The basic encoding in @eq:seahorn-shape fixes the semantic pieces of
$"VCGen_SeaHorn"$, but not their exact SMT shape. The implementation exposes
several equivalent or strengthening variants whose purpose is to help the SMT
solver propagate path choices, simplify definitions, or avoid irrelevant
terms.

==== CFG Variants

The CFG component can be encoded in several ways.

- backward, using predecessors:
  $bb_i => or_(j in "pred"(i)) bb_j$;
- forward, using successors:
  $bb_i => or_(j in "succ"(i)) bb_j$;
- with explicit edge variables $e_(i,j)$;
- forward plus backward edges to immediate dominators:
  $bb_i => bb_"idom"(i)$;
- with exclusivity constraints for incompatible choices, such as at-most-one
  selected successor or at-most-one selected predecessor.

For a diamond:

```tac
entry:
  c := havoc
  if c goto left else right

left:
  goto join

right:
  goto join
```

backward reachability for `join` says:

#logic-box[
  $
    bb_"join" => bb_"left" or bb_"right"
  $
]

whereas a forward encoding starts from `entry`:

#logic-box[
  $
    bb_"entry" => bb_"left" or bb_"right"
  $
]

An edge-variable encoding can make the selected edge explicit:

#logic-box[
  $
    e_("entry","left") &=> bb_"entry" and bb_"left" and c \
    e_("entry","right") &=> bb_"entry" and bb_"right" and not c
  $
]

Exclusivity constraints rule out spurious models that select both branches:

#logic-box[
  $
    not (bb_"left" and bb_"right")
  $
]

These constraints are logically redundant in an ideal path semantics, but they
can give the solver shorter Boolean-propagation paths.

==== Unguarded Static Definitions

Static definitions can either be guarded by their defining block or emitted as
top-level equations:

#logic-box[
  $
    bb_i => x = y + 1
  $

  $
    x = y + 1
  $
]

The unguarded form is sound for static SSA-style definitions when the symbol's
uses are already controlled by reachability constraints. If $x$ is unused, the
equation is simply irrelevant. If $x$ is used, exposing the equality at top
level lets the SMT solver eliminate the intermediate name early.

For example:

#logic-box[
  $
    x = y + 1 and z = x + 2
  $
]

can simplify by substitution to:

#logic-box[
  $
    z = y + 3
  $
]

This is the motivation for leaving definition guards optional: guarded
definitions preserve a direct path-scoped reading, while unguarded definitions
make algebraic simplification easier.

==== Phi as ITE

Phi constraints can be emitted as edge-specific implications, as in
@eq:seahorn-phi:

#logic-box[
  $
    (bb_i and bb_j) => x = x_i
  $

  $
    (bb_k and bb_j) => x = x_k
  $
]

Alternatively, the merge can be expressed as one explicit defining equation:

#logic-box[
  $
    x = "ite"(bb_i, x_i, x_k)
  $
]

The ITE form makes the definition of $x$ syntactically explicit. The solver can
then decide whether to keep the ITE, pull it through a use site, or simplify it
after Boolean propagation has fixed the selected predecessor.

For example, after learning $bb_i$, the equation:

#logic-box[
  $
    x = "ite"(bb_i, x_i, x_k)
  $
]

collapses to:

#logic-box[
  $
    x = x_i
  $
]

==== Example 2: Optimized Diamond Encoding

Using the same diamond program from Example 1, choose:

- forward CFG constraints,
- unguarded static definitions,
- ITE encoding for the phi node.

Then the formula components become:

#logic-box[
  $
    #formula-part[CFG] &= bb_"entry" \
      &quad and (bb_"entry" => bb_"left" or bb_"right") \
      &quad and (bb_"left" => bb_"join") \
      &quad and (bb_"right" => bb_"join") \
      &quad and (bb_"join" => bb_"exit") \
      &quad and bb_"exit" \
    #formula-part[DEF] &=
      c = (x < y) \
      &quad and a_"left" = x + 1 \
      &quad and a_"right" = y + 1 \
      &quad and a = "ite"(bb_"left", a_"left", a_"right") \
      &quad and "ok" = (a > 0) \
    #formula-part[JUMPS] &=
      ((bb_"entry" and bb_"left") => c) \
      &quad and ((bb_"entry" and bb_"right") => not c) \
    #formula-part[PHI] &= top \
    #formula-part[ERROR] &= bb_"exit" => top and not "ok"
  $
]

The CFG constraints now push reachability forward from each selected block to a
successor. Static definitions are visible as top-level equations. The phi
component is empty because the merge is represented directly by the ITE
definition of $a$.

=== Common Soundness Pitfalls

The SeaHorn-style encoding is compact, but small changes can silently change
the meaning of the generated formula. The following mistakes have appeared in
the history of this encoder family.

==== Critical Edges

An edge $u -> v$ is critical when $u$ has more than one successor and $v$ has
more than one predecessor:

#align(center)[
  $ |"succ"(u)| > 1 and |"pred"(v)| > 1 $
]

#align(center)[#image("critical-edge.svg", width: 70%)]

The problem is that block variables do not identify which incoming edge was
taken. On a critical edge, $bb_u and bb_v$ may be true even when execution
reaches $v$ through a different predecessor.

For example:

```tac
entry:
  c := havoc
  if c goto join else mid

mid:
  goto join

join:
  ok := phi [entry: true, mid: false]
  goto exit

exit:
  assume true
  assert ok
  halt
```

The edge $"entry" -> "join"$ is critical: `entry` has two successors and `join`
has two predecessors. The real program is unsafe: when $c$ is false, execution
goes through `mid`, reaches `join`, sets `ok := false`, and fails the assert.

But if the encoder represents the true edge condition as:

#logic-box[
  $
    (bb_"entry" and bb_"join") => c
  $
]

then the feasible path `entry -> mid -> join` is incorrectly rejected, because
both $bb_"entry"$ and $bb_"join"$ are true on that path while $c$ is false.
The encoder can miss the bug.

The standard repair is to split critical edges by inserting a landing block:

```tac
entry:
  c := havoc
  if c goto entry_to_join else mid

entry_to_join:
  goto join

mid:
  goto join
```

Now the edge-specific condition is attached to the non-critical edge
$"entry" -> "entry_to_join"$ rather than to $"entry" -> "join"$.

Effect: this can cause *missing paths*. A real entry-to-exit execution is ruled
out by constraints that were meant for a different edge.

==== Missing Predecessor Exclusivity for ITE Merges

When a phi merge is encoded as implications, selecting two predecessors often
creates an immediate contradiction:

#logic-box[
  $
    (bb_i and bb_j) => x = x_i
  $

  $
    (bb_k and bb_j) => x = x_k
  $
]

If $x_i != x_k$ and both predecessors are selected, the equalities conflict.
With an ITE merge, however, the formula contains only one equality:

#logic-box[
  $
    x = "ite"(bb_i, x_i, x_k)
  $
]

If both $bb_i$ and $bb_k$ are true, the ITE simply chooses one arm. A model can
therefore satisfy the CFG part using an impossible merge state, and different
merged variables may be read from different incoming edges. The result is a
spurious counterexample: the formula describes a mixed state that no execution
can produce.

For example:

```tac
entry:
  c := havoc
  if c goto left else right

left:
  x_left := true
  p_left := true
  goto join

right:
  x_right := false
  p_right := false
  goto join

join:
  x := phi [left: x_left, right: x_right]
  p := phi [left: p_left, right: p_right]
  ok := x == p
  goto exit

exit:
  assume true
  assert ok
  halt
```

The program is safe. On the left path, both $x$ and $p$ are true. On the right
path, both are false. Now suppose the two phi nodes are emitted as independent
ITE definitions, and their incoming cases appear in different orders:

#logic-box[
  $
    x = "ite"(bb_"left", x_"left", x_"right")
  $

  $
    p = "ite"(bb_"right", p_"right", p_"left")
  $
]

If the CFG constraints allow both $bb_"left"$ and $bb_"right"$, then the first
ITE can choose the left value while the second chooses the right value. The
formula can set $x = "true"$ and $p = "false"$, making $"ok"$ false even
though no entry-to-exit execution reaches such a state.

The repair is an at-most-one predecessor constraint at the merge:

#logic-box[
  $
    not (bb_"left" and bb_"right")
  $
]

Equivalently, a CFG encoding that uses incoming edge variables must enforce
that at most one incoming edge to the merge fires.

Effect: this can cause *infeasible paths*. The formula admits a merge state that
does not correspond to any single predecessor edge.

==== Unguarded Path-Local Facts

Unguarded definitions are useful when the RHS is total and the definition is
static. They become dangerous when the RHS carries a path-local axiom or a
partial-operation side condition.

Consider a pseudo-operation `narrow64` whose encoding treats it as identity
but also adds a 64-bit range fact for its result:

```tac
entry:
  x := havoc
  small := x < 2^64
  if small goto narrow_block else exit

narrow_block:
  y := narrow64(x)
  goto exit

exit:
  assume not small
  assert false
  halt
```

The program is unsafe: choose $x >= 2^64$. Then `small` is false, execution
goes directly to `exit`, the assumption `not small` holds, and `assert false`
fails.

If `y := narrow64(x)` is emitted globally as:

#logic-box[
  $
    y = x and 0 <= y and y <= 2^64 - 1
  $
]

then the encoder has constrained $x$ even on the path that never reaches
`narrow_block`. On the failing path, `not small` requires $x >= 2^64$, while
the global range fact requires $x <= 2^64 - 1$. The bad encoding therefore
makes the failing path inconsistent.

The guarded form keeps the range fact local:

#logic-box[
  $
    bb_"narrow_block" => (y = x and 0 <= y and y <= 2^64 - 1)
  $
]

The same issue occurs for operator axioms whose validity depends on where the
operator call appears. Axioms for such calls must be guarded by the triggering
block, or otherwise justified as globally safe.

Effect: this can cause *missing paths*. Facts from an unvisited block constrain
an execution that should not see those facts.
