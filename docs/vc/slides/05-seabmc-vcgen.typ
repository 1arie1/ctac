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
  #text(size: 28pt)[SeaBMC Style]
]

== Idea

SeaBMC-style VCGen compiles control-dependence into data-dependence.

#v(0.25cm)

After preprocessing:

- no block variables are needed
- no separate CFG constraints are emitted
- phi nodes become ordinary `ite` definitions
- cone-of-influence reduction is just data-flow slicing

#v(0.25cm)
#text(fill: muted, size: 16pt)[SeaHorn kept the CFG in the formula;
Boogie compiled it into recursion; SeaBMC makes it *disappear*.]

== Gated SSA

A gamma node is a value-level merge:

#align(center)[
  $ x := gamma(g, x_t, x_f) $
]

It means:

#logic-box[
  $ x := "ite"(g, x_t, x_f) $
]

Unlike a phi node, `gamma` mentions a Boolean *program expression*, not a
predecessor block name.

== From Phi To Gamma

The branch condition `c` already decides the incoming region — let the
merge switch on *it*:

#diamond-cfg-full(
  phi-style: "ite",
  t-label: $c$, f-label: $not c$,
  join-note: [was: #text(font: "Menlo", size: 11pt)[a := phi \[left: a_left, right: a_right\]]],
)

#v(0.2cm)
`a := gamma(c, a_left, a_right)` desugars to
`a := ite(c, a_left, a_right)` — an ordinary SSA definition. No CFG
predicate needed to explain the merge.

== Flat VC

After phi elimination:

#logic-box[
  $
    "VCGen_SeaBMC"(P) =
      #formula-part[DEF] and #formula-part[ASSUME] and not #formula-part[ASSERT]
  $
]

For the diamond:

#logic-box[
  $
    #formula-part[DEF] =
      c = (x < y)
      and a_"left" = x + 1
      and a_"right" = y + 1
      and a = "ite"(c, a_"left", a_"right")
      and "ok" = (a > 0)
  $
]

#v(0.2cm)
No block variables, no CFG constraints. The only trace of control flow
is the ITE guard in the definition of `a`.

== Control Dependence

#align(center)[#image("../sections/control-dependence.svg", width: 62%)]

#compact-list[
- $d$ *postdominates* $b$: every path $b arrow.r$ `exit` passes through $d$.
- $b_1$ is *control-dependent* on branch $b_2$: some successor of $b_2$
  forces a later visit to $b_1$, while $b_1$ does not postdominate $b_2$
  itself — the branch genuinely decides.
]

== Gate Construction

For each block $b$, compute a Boolean expression `gate(b)` over *program*
branch conditions:

#logic-box[
  $
    "gate"("entry") &= top \
    "gate"(b) &=
      or_(c in "ctrl"(b)) ("gate"(c) and "orient"(c,b))
  $
]

- `ctrl(b)`: branch blocks $b$ is control-dependent on
  (empty #sym.arrow.r $"gate"(b) = top$).
- `orient(c,b)`: the branch condition of $c$, or its negation, depending
  on which successor reaches $b$.

In a structured diamond: $"gate"("left") = c$, $"gate"("right") = not c$.

== The Hidden Blow-Up

`gate` is recursive. Substituted textually into every use, shared
control structure is *copied*:

#logic-box[
  #set text(size: 14.5pt)
  $
    "gate"(c) &= (p and r) or (q and s) \
    "gate"(d) &= (q and t) or (#text(fill: rgb("#b91c1c"))[$(p and r) or (q and s)$] and u) \
    "gate"(e) &= (#text(fill: rgb("#b91c1c"))[$(p and r) or (q and s)$] and v) or
      ((q and t) or (#text(fill: rgb("#b91c1c"))[$(p and r) or (q and s)$] and u) and w)
  $
]

Every level repeats its ancestors; every gamma that uses $"gate"(e)$
repeats the whole tree again — *exponential* in the DAG depth.

== Materialized Gates

Name each gate as an ordinary Boolean SSA definition, and let gammas
refer to the names:

#logic-box[
  $
    G_"entry" &:= top \
    G_b &:= or_(c in "ctrl"(b)) (G_c and "orient"(c,b))
  $
]

For the blow-up example:

#logic-box[
  #set text(size: 14.5pt)
  $
    G_c := (G_a and r) or (G_b and s) quad quad
    G_d := (G_b and t) or (G_c and u) quad quad
    G_e := (G_c and v) or (G_d and w)
  $
]

The DAG is represented once — *linear* in gates plus uses. The VC stays
CFG-free: gates are just definitions.

== Materialized Gates In The Program

Gates are just definitions; the VC stays CFG-free:

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

`join1` and `join2` share the same control-dependence DAG — it appears
once, not once per merge.

== Thin GSSA

Materialization stops the copying, but gates can still enumerate every
path from `entry`. *Thin GSSA* switches only on the *direct*
control-dependence controllers:

#align(center)[
  $ K_(c,b) = G_c and "orient"(c,b) $
]

#v(0.2cm)

Why the $G_c$ factor? SSA variables are *total* in the formula:

#question-box[
  If controller block $c$ is never reached, its branch condition still
  has a model value. Switching on the condition alone lets an
  *unreachable* branch select the merge value.
]

$G_c$ says "controller $c$ itself is reached" — dead branch conditions
cannot fire a case.

== The Fallback: false And undef

If no direct-controller case fires, execution does not reach $b$:

#compact-list[
- For the *reachability gate* $G_b$, the fallback is `false` — not
  reached means not reached.
- For a *value* merge in $b$, the fallback is `undef`: a fresh,
  unconstrained symbol of the right type. The value is unobservable
  when $b$ is not reached — any value will do.
]

#align(center)[#image("../sections/thin-gssa.svg", width: 50%)]

== Thin GSSA, Derived

#align(center)[#image("../sections/thin-gssa-example-cfg.svg", width: 58%)]

The outer branch `c1` selects the region feeding `n`; the local branches
`c2`, `c3` only compute values *inside* each region.

== Thin GSSA, Derived: Three Steps

#alternatives[
  *Step 1 — regular GSSA*: each phi uses the full path condition of its
  predecessor:

  ```tac
  a_join:
    v_a := gamma(c1 and c2, v_x, gamma(c1 and not c2, v_a0, undef))

  b_join:
    v_b := gamma(not c1 and c3, v_y,
           gamma(not c1 and not c3, v_b0, undef))

  n:
    v := gamma(c1, v_a, gamma(not c1, v_b, undef))
  ```

  Every gate repeats the outer condition `c1`.
][
  *Step 2 — drop dead fallbacks*: the program is SESE, so execution
  reaching a join arrives from exactly one predecessor — complete
  two-way choices never select `undef`:

  ```tac
  a_join:
    v_a := gamma(c2, v_x, gamma(not c2, v_a0, undef))

  b_join:
    v_b := gamma(c3, v_y, gamma(not c3, v_b0, undef))

  n:
    v := gamma(c1, v_a, v_b)
  ```

  The local gates no longer mention `c1` — the *direct* controller is
  enough.
][
  *Step 3 — thin form*, after collapsing the two-way choices and
  desugaring gamma:

  ```tac
  a_join:
    v_a := ite(c2, v_x, v_a0)

  b_join:
    v_b := ite(c3, v_y, v_b0)

  n:
    v := ite(c1, v_a, v_b)
  ```

  The final merge at `n` depends *only* on the region selector `c1`;
  each local ITE depends only on its own branch. Path conditions never
  materialize.
]

== Cone Of Influence

Once control is data:

1. Start from the exit `assume` and `assert`.
2. Keep each used variable definition.
3. Add the variables used by that definition.
4. Keep gates only when retained ITEs use them.
5. Drop every unmarked definition.

No graph reachability rule is needed for pruning.

== COI Example

```tac
n:
  v := ite(c1, v_a, v_b)
  junk := expensive(v_x, v_y)
  ok := v > 0

exit:
  assume true
  assert ok
```

`junk` is dropped because it is not used by `ok`, the exit assumption, or a
retained gate.

#v(0.2cm)
A branch that gates no retained value simply vanishes from the formula.

== Three Encodings, One Diamond

#{
  set text(size: 15pt)
  table(
    columns: (auto, 1fr, 1fr, 1fr),
    stroke: 0.5pt + rgb("#cbd5e1"),
    inset: 7pt,
    table.header([], [*SeaHorn* (03)], [*Boogie* (04)], [*SeaBMC* (05)]),
    [control flow], [explicit: $bb_i$ variables + path constraints],
      [recursion: backward $"ok"_i$ equations],
      [compiled away: gates as data],
    [program form], [SSA], [DSA], [SSA #sym.arrow.r gated SSA],
    [joins], [PHI edge implications / ITE], [DSA edge definitions],
      [gamma over branch conditions],
    [formula shape], [flat conjunction], [nested implications],
      [flat conjunction, CFG-free],
    [solver lever], [top-level equalities, Boolean propagation on $bb_i$],
      [assertions and assumes for free],
      [substitution and slicing everywhere],
    [watch out for], [critical edges, merge exclusivity, unguarded facts],
      [exclusivity for phi/ITE extensions],
      [gate blow-up without materialization],
  )
}

#v(0.2cm)
#text(fill: muted, size: 15pt)[ctac's default encoder (`sea_vc`) is
SeaHorn-style — block variables over DSA — with the guarded/unguarded
and merge-shape choices exposed as flags.]
