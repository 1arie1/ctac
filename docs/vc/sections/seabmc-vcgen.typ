#import "tac-code.typ": tac-code, logic-box
#show raw.where(lang: "tac"): it => tac-code(it.text)
#let formula-part(body) = text(fill: rgb("#0369a1"), weight: "semibold")[#body]
#let def-term(body) = text(fill: rgb("#0369a1"), weight: "bold")[#body]

== SeaBMC-Style VCGen

Our goal is a VCGen algorithm that does not need separate CFG constraints, as
in the Boogie-style encoding, but remains direct, as in the SeaHorn-style
encoding.

The intuition is to reduce all control-dependence into data-dependence, so that
program statements can execute in arbitrary order, and the assertion and
assumption use only the values they require.

Assume that $P$ is in SSA, SESE, and SASA form: every variable is assigned only
once, joins are represented by phi nodes, all paths go from `entry` to `exit`,
and the designated exit block contains the single assumption and assertion.

Direct phi encoding needs CFG information. The trick is to rewrite the input
program so phi nodes disappear before VC generation. In compilers, this form is
known as *Gated SSA*. A phi node is replaced by a gamma node guarded by Boolean
program expressions rather than by predecessor block names.

=== Gated SSA

A gamma node is a value-level merge:

#align(center)[
  $x := gamma(g, x_t, x_f)$
]

It means that $x$ takes $x_t$ when the guard $g$ is true, and $x_f$ when the
guard is false. Unlike a phi node, a gamma node does not mention predecessor
blocks or any auxiliary block-reachability variables. It mentions only ordinary
program expressions.

Consider the running diamond in SSA form:

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

In Gated SSA, the phi node is replaced by a gamma node guarded by the branch
condition that controls the choice:

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
  a := gamma(c, a_left, a_right)
  ok := a > 0
  goto exit

exit:
  assume true
  assert ok
  halt
```

Gamma nodes add no new semantics. We use `gamma` only as syntactic sugar for
an ITE expression:

#logic-box[
  $
    x := gamma(g, x_t, x_f) quad "means" quad x := "ite"(g, x_t, x_f)
  $
]

Thus the example above is interpreted as:

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

After this rewrite, the merge assignment for `a` is an ordinary SSA
definition. It no longer needs a CFG predicate to explain which incoming edge
was taken.

=== Gate Construction

The GSSA conversion computes, for each block $b$, a Boolean expression
$"gate"(b)$ that is true exactly when execution reaches $b$, but written in
terms of program branch conditions rather than block variables.

We define #def-term[control-dependence] using #def-term[postdominators]. A
block $d$ #def-term[postdominates] block $b$ when every path from $b$ to `exit`
goes through $d$. A block $b_1$ is #def-term[control-dependent] on branch block
$b_2$ iff:

- $b_2$ has a successor $s$ such that $b_1$ postdominates $s$;
- $b_1$ does not postdominate $b_2$.

Intuitively, after execution takes edge $b_2 -> s$, it must eventually reach
$b_1$. Before the branch at $b_2$ is resolved, however, reaching $b_1$ is not
forced. This is illustrated in @fig:control-dependence.

The #def-term[control-dependence graph] has one node for each basic block and
an edge $c -> b$ whenever $b$ is control-dependent on branch block $c$ by the
definition above. Thus the edge points from the controlling branch block to the
block whose execution it controls.

#figure(
  placement: top,
  image("control-dependence.svg", width: 82%),
  caption: [
    Block $b_1$ is control-dependent on branch block $b_2$: the edge
    $b_2 -> s$ forces a later visit to $b_1$, while the other branch can
    bypass $b_1$.
  ],
) <fig:control-dependence>

Let $"ctrl"(b)$ be the set of branch blocks on which $b$ is control-dependent.
A controller $c in "ctrl"(b)$ is therefore a basic block whose terminator is a
conditional branch. Define $"orient"(c,b)$ as:

- the branch condition of $c$ when $b$ lies under the true successor of $c$;
- the negated branch condition when $b$ lies under the false successor of $c$.

In @fig:control-dependence, $s$ is the true successor of $b_2$. Therefore, if
the branch condition at $b_2$ is $g$, then $"orient"(b_2,b_1) = g$. The other
successor $t$ is the false successor, so a block controlled by the $t$ branch
would use the orientation $not g$.

The gate equations are:

#math.equation(block: true, numbering: "(1)", $
  "gate"("entry") &= top \
  "gate"(b) &=
    or_(c in "ctrl"(b)) ("gate"(c) and "orient"(c,b))
$) <eq:seabmc-gate>

When $"ctrl"(b)$ is empty, $"gate"(b) = top$. In a structured diamond,
$"gate"("left") = c$ and $"gate"("right") = not c$.

For a phi node in block $j$:

```tac
j:
  x := phi [p1: v1, p2: v2, ..., pn: vn]
```

replace it with a nested gamma expression over the predecessor gates:

#logic-box[
  $
    x := gamma("gate"(p_1), v_1,
         gamma("gate"(p_2), v_2,
         dots
         gamma("gate"(p_(n-1)), v_(n-1), v_n)))
  $
]

For a two-predecessor join, this is simply:

#logic-box[
  $
    x := gamma("gate"(p_1), v_1, v_2)
  $
]

The case order is irrelevant when the gates are mutually exclusive on real
executions. For readability, examples use the branch condition directly when it
is syntactically equal to the predecessor gate.

=== Conversion Algorithm

The SSA-to-GSSA conversion is a source-to-source pass.

1. Compute postdominators and control-dependence for the CFG.
2. For every block $b$ that can be used by a merge, compute $"gate"(b)$ from
   @eq:seabmc-gate in topological order over the control-dependence relation.
3. For every phi node, replace each predecessor label by the predecessor gate.
4. Emit the resulting gamma expression as an ordinary `ite`.
5. Delete the phi node.

After the pass, the program contains only ordinary assignments, havoc commands,
the final assumption, and the final assertion. Its VC is the flat conjunction:

#math.equation(block: true, numbering: "(1)", $
  "VCGen_SeaBMC"(P) =
    "DEF" and "ASSUME" and not "ASSERT"
$) <eq:seabmc-shape>

where `DEF` is the conjunction of all assignment equalities after phi
elimination. Havoc assignments contribute no equality.

For the GSSA diamond above:

#logic-box[
  $
    #formula-part[DEF] &=
      c = (x < y) \
      &quad and a_"left" = x + 1 \
      &quad and a_"right" = y + 1 \
      &quad and a = "ite"(c, a_"left", a_"right") \
      &quad and "ok" = (a > 0) \
    #formula-part[ASSUME] &= top \
    #formula-part[ASSERT] &= "ok" \
    #formula-part[VC] &= #formula-part[DEF] and top and not "ok"
  $
]

The formula has no block variables and no separate CFG constraints. The only
remaining trace of control flow is the ITE guard in the definition of `a`.

=== Materialized Gates

The previous description hides a possible exponential blow-up. The definition
of $"gate"(b)$ is recursive: it may mention gates of controller blocks, which
may mention gates of their own controllers. If every gate expression is
substituted textually into every gamma node, shared control-dependence prefixes
are copied at each use. A gate DAG can therefore become an exponentially large
Boolean expression tree.

#def-term[Materialized gates] avoid this by introducing ordinary Boolean SSA
variables for gate predicates. Rather than guarding each gamma by a fully
expanded expression, the conversion introduces one named gate for each needed
block and lets gammas refer to those names.

The materialized form is:

#logic-box[
  $
    G_"entry" &:= top \
    G_b &:= or_(c in "ctrl"(b)) (G_c and "orient"(c,b)) \
    x &:= gamma(G_p, v_p, v_q)
  $
]

Here each $G_b$ is assigned once. The definitions may still form a DAG of
control-dependence, but the DAG is represented directly instead of being
duplicated into every use site.

==== Computing Materialized Gates

The materializing conversion is:

1. Compute postdominators and control-dependence.
2. Mark every predecessor block that is mentioned by a phi node. These blocks
   need gates because the corresponding gamma cases must be guarded.
3. Close the marked set under controllers: if $b$ is marked, mark every
   $c in "ctrl"(b)$. Repeat to a fixed point.
4. Emit one Boolean SSA definition $G_b$ for every marked block, in topological
   order over the control-dependence relation.
5. Replace each phi node with a gamma node guarded by the corresponding $G_p$
   variables.
6. Emit gamma nodes as ordinary `ite` expressions.

The resulting VC shape is still CFG-free. The CFG is used only by the
preprocessing pass that computes gate definitions. After that, the VC contains
ordinary assignment equalities, assumptions, and the negated assertion.

==== Example 1: Shared Gate Structure

Materialized gates help when several merges reuse the same control-dependence
structure. Consider a program whose gates have this shape:

#logic-box[
  $
    "gate"(a) &= p \
    "gate"(b) &= q \
    "gate"(c) &= ("gate"(a) and r) or ("gate"(b) and s) \
    "gate"(d) &= ("gate"(b) and t) or ("gate"(c) and u) \
    "gate"(e) &= ("gate"(c) and v) or ("gate"(d) and w)
  $
]

Suppose two phi nodes use the predecessor gates for $d$ and $e$:

```tac
join1:
  x := phi [d: x_d, e: x_e]

join2:
  y := phi [d: y_d, e: y_e]
```

The non-thin conversion substitutes the full expressions for $"gate"(d)$ and
$"gate"(e)$ into both gamma nodes:

#logic-box[
  $
    x &:= gamma("gate"(d), x_d,
           gamma("gate"(e), x_e, x_"other")) \
    y &:= gamma("gate"(d), y_d,
           gamma("gate"(e), y_e, y_"other"))
  $
]

If the gates are then expanded textually, both $x$ and $y$ contain copies of
$"gate"(e)$, each copy contains a copy of $"gate"(d)$ and $"gate"(c)$, and the
copying continues through the shared ancestors. Adding more joins that use the
same gates repeats the whole tree again.

The materialized-gate form shares the gates once:

```tac
gate_a := p
gate_b := q
gate_c := ite(gate_a, r, false) or ite(gate_b, s, false)
gate_d := ite(gate_b, t, false) or ite(gate_c, u, false)
gate_e := ite(gate_c, v, false) or ite(gate_d, w, false)

join1:
  x := gamma(gate_d, x_d, gamma(gate_e, x_e, x_other))

join2:
  y := gamma(gate_d, y_d, gamma(gate_e, y_e, y_other))
```

Equivalently, after desugaring gamma:

```tac
gate_a := p
gate_b := q
gate_c := (gate_a and r) or (gate_b and s)
gate_d := (gate_b and t) or (gate_c and u)
gate_e := (gate_c and v) or (gate_d and w)

join1:
  x := ite(gate_d, x_d, ite(gate_e, x_e, x_other))

join2:
  y := ite(gate_d, y_d, ite(gate_e, y_e, y_other))
```

Now the shared control-dependence structure is linear in the number of gate
definitions plus the number of gamma uses.

=== Thin Gated SSA

Materializing gates prevents repeated expansion, but it does not by itself make
the gates small. #def-term[Thin Gated SSA] uses only the *direct*
control-dependence controllers of a block instead of enumerating every complete
path from `entry` to that block.

A block $b$ is #def-term[directly control-dependent] on a branch block $c$ when
there is an edge $c -> b$ in the control-dependence graph. A block $b$ is
control-dependent on $c$ in the broader, transitive sense when $c$ reaches $b$
by a path of one or more control-dependence edges. Thin GSSA uses only the
one-edge controllers of $b$ as gamma cases. Controllers that are farther away
are not repeated in those cases; they are referenced through the
already-materialized gate $G_c$.

The ITE is over the direct controllers, but the case predicate for a controller
$c$ is not just $"orient"(c,b)$. It is:

#align(center)[
  $K_(c,b) = G_c and "orient"(c,b)$
]

The factor $G_c$ says that controller block $c$ itself is reached. Without it,
the branch condition of an unreachable controller could still choose a case,
because ordinary SSA variables are total in the formula. For example, if block
`a` is not reached, its branch condition `c2` may still have a model value;
switching on `c2` alone could incorrectly select the `a`-side incoming value.

If no direct-controller case $K_(c,b)$ fires, execution does not reach $b$. For
the Boolean reachability gate, the fallback is `false`. For a value gamma in
$b$, the fallback can be `undef`, because the value is unobservable when $b$ is
not reached. This distinction is illustrated in @fig:thin-gssa.

#figure(
  placement: top,
  image("thin-gssa.svg", width: 82%),
  caption: [
    Thin GSSA keeps the incoming cases for `n`: the branch from `entry` selects
    the `a` region under `c1` and the `b` region under `not c1`. The local
    branches controlled by `c2` and `c3` go elsewhere, so they are not incoming
    cases for `n` and collapse to the `undef` fallback.
  ],
) <fig:thin-gssa>

An `undef` value is an arbitrary value of the right type. In the VC, it is a
fresh unconstrained symbol. It is used as the fallback arm that makes the gamma
syntactically total, not as a demand-driven deletion of a verification-irrelevant
case.

For a block $b$ with direct controllers $c_1, dots, c_k$, the thin
reachability gate is:

#logic-box[
  $
    G_b =
      or_(i = 1)^k (G_(c_i) and "orient"(c_i, b))
  $
]

For a value merge in $b$, the same direct-controller cases guard the incoming
values, with an `undef` fallback:

#logic-box[
  $
    x :=
      gamma(K_(c_1,b), v_1,
      gamma(dots,
      gamma(K_(c_k,b), v_k, "undef")))
  $
]

The thin construction therefore switches only on the direct-controller cases,
but each case is guarded by both the controller's reachability and the
controller's oriented branch condition. Bypass cases are outside the direct
control-dependence cases for $b$, so value merges collapse them to `undef`.

==== Computing TGSSA

The thin conversion is a control-dependence pass:

1. Compute postdominators and the direct control-dependence relation.
2. For each block $b$, compute $"ctrl"(b)$, the direct controller blocks sorted
   closest-to-$b$ first.
3. For each controller $c in "ctrl"(b)$, compute $"orient"(c,b)$ from the
   controller's branch condition.
4. Build $G_b$ from the direct controller cases only, with `false` as the
   fallback case.
5. Materialize the required $G_b$ variables in topological order.
6. Rewrite phi nodes and dynamic merge cases to use the materialized $G_b$
   variables.

==== Example 2: Thin GSSA

The running diamond does not show the benefit: it has exactly two cases and no
side branches. The benefit appears when one condition controls the incoming
regions for a merge, while other branches remain local to those regions.

#figure(
  placement: top,
  image("thin-gssa-example-cfg.svg", width: 82%),
  caption: [
    CFG for the Thin GSSA example. The incoming regions for the phi at `n` are
    selected by `c1` and `not c1`. The local branches `c2` and `c3` only choose
    paths inside those regions before they reconverge at `a_join` and `b_join`.
  ],
) <fig:thin-gssa-example-cfg>

```tac
entry:
  c1 := havoc
  if c1 goto a else b

a:
  c2 := havoc
  v_a0 := 10
  if c2 goto x else a_join

x:
  v_x := 2
  goto a_join

a_join:
  v_a := phi [a: v_a0, x: v_x]
  goto n

b:
  c3 := havoc
  v_b0 := 20
  if c3 goto y else b_join

y:
  v_y := 3
  goto b_join

b_join:
  v_b := phi [b: v_b0, y: v_y]
  goto n

n:
  v := phi [a_join: v_a, b_join: v_b]
  assert v > 0
```

The phi at `n` merges the value produced by the `a` region with the value
produced by the `b` region. The outer branch selects those regions: `c1` selects
the `a` region, and `not c1` selects the `b` region. The local branches `c2`
and `c3` only decide how each region computes its own value.

In regular GSSA, each phi is converted independently by using the full path
condition for each incoming predecessor:

```tac
a_join:
  v_a := gamma(c1 and c2, v_x, gamma(c1 and not c2, v_a0, undef))

b_join:
  v_b := gamma(not c1 and c3, v_y,
         gamma(not c1 and not c3, v_b0, undef))

n:
  v := gamma(c1, v_a, gamma(not c1, v_b, undef))
```

In the last block, the left and right gate variables have already been inlined
as `c1` and `not c1`. Since the source program is SESE, every real execution
that reaches `n` arrives from exactly one predecessor. Thus the final `undef`
fallback in the gamma for `n` is never selected on a real execution and can be
dropped:

```tac
a_join:
  v_a := gamma(c2, v_x, gamma(not c2, v_a0, undef))

b_join:
  v_b := gamma(c3, v_y, gamma(not c3, v_b0, undef))

n:
  v := gamma(c1, v_a, v_b)
```

The same cleanup applies to the local phis, whose branch conditions are also
complete two-way choices. The final form is:

```tac
a_join:
  v_a := gamma(c2, v_x, v_a0)

b_join:
  v_b := gamma(c3, v_y, v_b0)

n:
  v := gamma(c1, v_a, v_b)
```

Equivalently, after desugaring gamma:

```tac
a_join:
  v_a := ite(c2, v_x, v_a0)

b_join:
  v_b := ite(c3, v_y, v_b0)

n:
  v := ite(c1, v_a, v_b)
```

=== Cone of Influence

Once the program is in data-flow form, cone-of-influence reduction is simple.
There are no CFG constraints to keep in sync with the program: every semantic
dependency is an ordinary expression dependency. The reducer can start from the
exit assumption and assertion and walk definitions backward.

The important point is that gates are ordinary Boolean definitions too. A gate
definition is kept only when some retained gamma uses it. Branch conditions are
then kept only when they are needed to define a retained gate. Branches that do
not gate any retained value may remain unconstrained or be dropped from the
data-flow formula.

==== COI Algorithm

Let $"defs"$ map each SSA variable to its unique defining expression after phi
nodes have been converted to gamma/ITE expressions. Let $"uses"(e)$ be the
variables used by expression $e$.

1. Initialize the worklist with every variable used by the exit `assume` and
   `assert`.
2. While the worklist is non-empty, remove a variable $x$.
3. If $x$ has no definition, keep its declaration and continue. This covers
   havoc inputs and `undef` symbols.
4. Keep the definition $x := e$.
5. Add every variable in $"uses"(e)$ to the worklist.
6. If $e$ is a gamma/ITE whose guard is a gate $G_b$, mark $G_b$ as needed.
7. Whenever a gate $G_b$ is marked, keep its definition and recursively mark
   the gates and branch-condition variables used by that definition.
8. Drop every unmarked definition.

The output is the same data-flow program restricted to the retained
definitions. Since every retained expression still names only retained
dependencies or free inputs, the reduced VC has the same value for the exit
assumption and assertion as the unreduced data-flow VC.

==== Example 3: COI Reduction

Consider the final Thin GSSA form above, with an extra value that is computed
but never reaches the assertion:

```tac
a_join:
  v_a := ite(c2, v_x, v_a0)

b_join:
  v_b := ite(c3, v_y, v_b0)

n:
  v := ite(c1, v_a, v_b)
  junk := expensive(v_x, v_y)
  ok := v > 0

exit:
  assume true
  assert ok
```

The COI walk starts from `ok`. It keeps:

```tac
n:
  ok := v > 0
  v := ite(c1, v_a, v_b)

a_join:
  v_a := ite(c2, v_x, v_a0)

b_join:
  v_b := ite(c3, v_y, v_b0)
```

and drops:

```tac
n:
  junk := expensive(v_x, v_y)
```

because `junk` is not used by `ok`, the exit assumption, or any retained gate.
No graph reachability rule is needed for this pruning; ordinary backwards
data-dependence is enough after the GSSA conversion.
