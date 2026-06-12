#import "@preview/touying:0.7.4": *
#import themes.simple: *
#import "../sections/tac-code.typ": tac-code

#show: simple-theme.with(aspect-ratio: "16-9")

#show raw.where(lang: "tac"): it => tac-code(
  it.text,
  font: "Consolas for Powerline",
  font-size: 12pt,
  inset: (x: 9pt, y: 7pt),
)

#set text(font: "Verdana", size: 18pt)
#set par(justify: false)

#let muted = rgb("#475569")

#let two-col(left, right) = grid(
  columns: (1fr, 1fr),
  gutter: 0.7cm,
  left,
  right,
)

#title-slide[
  #text(size: 46pt, weight: "bold")[Tiny TAC]
  #v(0.2cm)
  #text(size: 30pt)[Syntax And Semantics]
]

== Tiny TAC

*Tiny TAC* (`ttac`) is the small language used in the VCGen notes.

It keeps only the semantic core needed for examples:

- typed registers: `bool`, `int`, `bytemap`
- assignments, havoc, assume, assert
- basic blocks with explicit terminators
- phi nodes at joins

#v(0.25cm)
#text(fill: muted)[The goal is not to document ctac syntax. The goal is to make
the VCGen algorithms precise.]

== Types And Expressions

#two-col[
  Registers have one of three types:

  #align(center)[
    $ tau ::= "bool" | "int" | "bytemap" $
  ]

  The SMT model is intentionally direct:

  #align(center)[
    $ "int" mapsto "Int" $
  ]

  #align(center)[
    $ "bytemap" mapsto "Int" -> "Int" $
  ]
][
  Core integer expressions:

  #align(center)[
    $ i ::= n | x | i + i | i - i | i * i | i / i $
  ]

  Boolean expressions:

  #align(center)[
    $ b ::= "true" | "false" | c | i < i | i <= i | b and b $
  ]

  `ite` is an expression operator, not a structured statement.
]

== Maps

Loads and stores are expressions over bytemaps.

```tac
M := havoc
i := havoc
v := havoc
x := M[i]
M2 := M[i := v]
```

#v(0.25cm)
Semantically, `M2` agrees with `M` at every address except `i`, where it
stores `v`.

== Commands

#two-col[
  Command forms:

  ```text
  x := e
  x := havoc
  x := phi [B1: x1, B2: x2]
  assume b
  assert c
  ```

  `:=` is assignment. Equality is a separate expression/operator.
][
  Example:

  ```tac
  x := havoc
  y := havoc
  z := havoc
  c := x < y
  assume y < z
  assert c
  ```

  `assume` may use an expression. `assert` uses a named bool register.
]

== Blocks And Control

Unstructured basic blocks. Branches are terminators.

```tac
entry:
  x := havoc
  y := havoc
  c := x < y
  if c goto ok else bad

ok:
  assert c
  goto exit

bad:
  assume not c
  halt

exit:
  halt
```

== Phi Nodes

Phi nodes select by predecessor block.

```tac
L:
  xl := 1
  goto J

R:
  xr := 2
  goto J

J:
  x := phi [L: xl, R: xr]
  goto exit
```

- Enter from `L`: `x := xl`
- Enter from `R`: `x := xr`

== Semantic Contract

A `ttac` execution follows the expected operational semantics:

- assignment updates the destination register
- havoc chooses an arbitrary value of the destination type
- assume filters executions
- assert fails when its named condition is false
- terminators choose the next block

#v(0.35cm)
VC generation is bug-oriented:

#align(center)[
  $ "VCGen"(P) " is satisfiable " <=> P " has an assertion-failure execution" $
]
