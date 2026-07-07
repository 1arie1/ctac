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
  #text(size: 46pt, weight: "bold")[Tiny TAC]
  #v(0.2cm)
  #text(size: 30pt)[Syntax, Semantics, Demo]
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
  Integer expressions:

  #align(center)[
    $ i ::= &n | x | M[i] \
        | &i + i | i - i | i * i | i \/ i \
        | &"ite"(b, i, i) $
  ]

  Boolean expressions:

  #align(center)[
    $ b ::= &"true" | "false" | c \
        | &i < i | i <= i | i = i | b = b \
        | &not b | b and b | b or b \
        | &"ite"(c, b, b) $
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

A complete program — `safe_core.ttac`, the running example of this deck:

#two-col(columns: (1.25fr, 1fr))[
  ```tac
  entry:
    M := havoc
    i := havoc
    limit := havoc
    x := M[i]
    y := x + 1
    M2 := M[i := y]
    c := y <= limit
    if c goto ok else bad

  ok:
    assert c
    goto exit
  ```
][
  ```tac
  bad:
    assume not c
    goto exit

  exit:
    halt
  ```

  #v(0.2cm)
  Unstructured basic blocks; branches are terminators and branch on a
  *named* bool register.

  Both branches rejoin at `exit` — every block is on an entry-to-exit
  path. The assert in `ok` only runs on the `c`-true path.
]

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

== Demo: First Look At A Program

`ttac stats` reads the surface — commands, types, memory capability:

#term-box[
  #sh[ttac stats safe_core.ttac --plain]
  #out[overview.blocks: 4 #h(3.2em) overview.commands: 9]
  #out[command_kinds.Assign: 4 #h(1em) Havoc: 3 #h(1em) Assert: 1 #h(1em) Assume: 1]
  #out[types.int: 4 #h(5.1em) types.bool: 1 #h(1em) types.bytemap: 2]
  #out[memory.capability: bytemap-rw #h(1em) loads: 1 #h(1em) updates: 1]
  #out[shape.asserts: 1]
]

#v(0.3cm)
Four blocks, one assert, read-write bytemap use — matches the program
on the previous slide.

== Demo: Semantics, Executed

The interpreter *is* the operational semantics. Zero-havoc run:

#term-box[
  #sh[ttac run safe_core.ttac --trace]
  #hi[status: done (finished) #h(2em) assert_ok: 0 #h(2em) assert_fail: 0]
  #out[entry:]
  #out[#h(1.2em) M := havoc #h(6.2em) \# havoc bytemap]
  #out[#h(1.2em) i := havoc  = 0]
  #out[#h(1.2em) limit := havoc  = 0]
  #out[#h(1.2em) x := M\[i\]  = 0 #h(4.6em) \# M\[0\]]
  #out[#h(1.2em) y := x + 1  = 1]
  #out[#h(1.2em) M2 := M\[i := y\] #h(3.4em) \# M\[0 := 1\]]
  #out[#h(1.2em) c := y \<= limit  = false]
  #out[#h(1.2em) if c goto ok else bad #h(1em) \# c=false -> bad]
  #out[bad:]
  #out[#h(1.2em) assume not c #h(4.6em) \# assume: true]
  #out[#h(1.2em) goto exit #h(6.4em) \# -> exit]
  #out[exit:]
  #out[#h(1.2em) halt #h(9.4em) \# halt]
]

#pause
#v(0.2cm)
Havoc defaulted to `0`, so `c` is false and execution takes the `bad`
path — the assert never runs. One execution, not all of them.

== Demo: Asking About All Executions

`assert c` in block `ok` — can it *ever* fail?

#term-box[
  #sh[ttac vcgen safe_core.ttac --solve]
  #hi[unsat]
]

#v(0.2cm)
#unsat-chip #h(0.4em) no execution reaches `ok` with `c` false — the
branch guard protects the assert on *every* path.

#pause
#v(0.4cm)

That is the VCGen contract, seen end to end:

#align(center)[
  $ "VCGen"(P) " is satisfiable " <=> P " has an assertion-failure execution" $
]

#v(0.2cm)
#text(fill: muted, size: 16pt)[
  Interpreter: one chosen execution. Solver: a question over all of them.
]
