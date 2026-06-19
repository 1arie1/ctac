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

== Gated SSA

A gamma node is a value-level merge:

#align(center)[
  $ x := gamma(g, x_t, x_f) $
]

It means:

#logic-box[
  $ x := "ite"(g, x_t, x_f) $
]

Unlike a phi node, `gamma` mentions a Boolean program expression, not a
predecessor block name.

== SSA Diamond

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
```

== GSSA Diamond

The branch condition `c` selects the incoming region.

```tac
join:
  a := gamma(c, a_left, a_right)
  ok := a > 0
  goto exit
```

After desugaring:

```tac
join:
  a := ite(c, a_left, a_right)
  ok := a > 0
  goto exit
```

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

== Gate Construction

For each block `b`, compute a Boolean expression `gate(b)`:

#logic-box[
  $
    "gate"("entry") &= top \
    "gate"(b) &=
      or_(c in "ctrl"(b)) ("gate"(c) and "orient"(c,b))
  $
]

`ctrl(b)` contains controlling branch blocks. `orient(c,b)` is the branch
condition or its negation, depending on which successor reaches `b`.

== Control Dependence

#align(center)[#image("../sections/control-dependence.svg", width: 82%)]

A block is control-dependent on a branch when one successor forces a later visit
to the block, while another successor can bypass it.

== Materialized Gates

Expanding every gate at every use can duplicate shared control structure.

Materialized gates introduce ordinary SSA Boolean definitions:

#logic-box[
  $
    G_"entry" &:= top \
    G_b &:= or_(c in "ctrl"(b)) (G_c and "orient"(c,b)) \
    x &:= gamma(G_p, v_p, v_q)
  $
]

The VC remains CFG-free; gates are just definitions.

== Shared Gate Example

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

The shared control-dependence DAG is represented once.

== Thin GSSA

Thin GSSA uses only direct control-dependence controllers.

#align(center)[#image("../sections/thin-gssa.svg", width: 82%)]

For a direct controller `c` of block `b`:

#align(center)[
  $ K_(c,b) = G_c and "orient"(c,b) $
]

The `G_c` factor prevents unreachable branch conditions from selecting values.

== Thin Example CFG

#align(center)[#image("../sections/thin-gssa-example-cfg.svg", width: 82%)]

The outer branch selects the region feeding `n`; local branches only compute
values inside each region.

== Thin Example: Final Form

```tac
a_join:
  v_a := ite(c2, v_x, v_a0)

b_join:
  v_b := ite(c3, v_y, v_b0)

n:
  v := ite(c1, v_a, v_b)
```

The final phi at `n` depends only on the region selector `c1`, not on the local
branch choices `c2` and `c3`.

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
