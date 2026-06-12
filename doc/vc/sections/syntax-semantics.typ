#import "tac-code.typ": tac-code
#show raw.where(lang: "tac"): it => tac-code(it.text)

= Syntax and Semantics of the Target Language

We use a small TAC-like language as the source of VC generation. It keeps the
semantic core explicit and leaves implementation-specific details out of scope.

== Types

Registers have one of three types:

#align(center)[
  $ tau ::= "bool" | "int" | "bytemap" $
]

An $"int"$ is modeled as an SMT $"Int"$. A $"bytemap"$ is an integer-indexed
integer map:

#align(center)[
  $ "bytemap" = "int" -> "int" $
]

We write $x : tau$ to say that register $x$ has type $tau$.

== Expressions

```text
i ::= n
    | x
    | M[i]
    | i + i
    | i - i
    | i * i
    | i / i
    | ite(b, i, i)

b ::= true
    | false
    | c
    | i <= i
    | i < i
    | i == i
    | b == b
    | not b
    | b and b
    | b or b
    | ite(c, b, b)
```

Here $x$ ranges over integer registers and $c$ ranges over bool registers. The
operator `/` denotes SMT integer division. The conditional operator is
expression-level if-then-else.

```text
m ::= M
    | M[i := v]

v ::= i
```

A load is an integer expression; a store produces a new bytemap value:

```tac
M := havoc
i := havoc
v := havoc
x := M[i]
M2 := M[i := v]
```

== Commands

```text
cmd ::= x := e
      | x := havoc
      | x := phi [B1: x1, B2: x2, ...]
      | assume b
      | assert c
```

The expression $e$ has the same type as $x$. The special value `havoc` denotes
an arbitrary value of that type. Phi commands use the LLVM-style predecessor
list, with `:=` retained as the assignment marker.

Assumptions may mention arbitrary bool expressions. Assertions use a purified
condition: the assertion argument is a bool register, not an arbitrary
expression.

For example:

```tac
x := havoc
y := havoc
z := havoc
c := x < y
assume y < z
assert c
```

Thus `assert` conditions are named, while `assume` conditions need not be.

== Blocks and Programs

A program is a collection of basic blocks connected by terminators.

```text
block ::= B:
            cmd*
            terminator

terminator ::= halt
             | goto B
             | if c goto B1 else B2
```

Conditional terminators branch on a bool register, so every branch condition is
named.

A program has a distinguished entry block and a distinct exit block:

```text
program ::= entry = B_entry
            exit  = B_exit
            block*
```

The exit block is the normal target for completed executions; `halt` stops
execution at the current block.

== Example

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

bad:
  assume not c
  halt

exit:
  halt
```

The conditional branch is the terminator of `entry`; the assertion in `ok`
refers to the named bool register `c`.

== Semantic Intuition

The language follows the expected operational semantics. Assignments update the
destination register. A havoc assignment chooses an arbitrary value of the
destination type. A load reads a map at an integer address; a store returns a
new map that agrees with the old map except at the updated address.

`assume b` keeps only executions where $b$ is true.

`assert c` fails when the named bool register $c$ is false. VC generation is
oriented toward this failure condition: the generated formula is satisfiable
exactly when such a failure execution exists.

A conditional terminator `if c goto B1 else B2` transfers control to $"B1"$ when
$c$ is true and to $"B2"$ when $c$ is false.

Phi commands select the value associated with the predecessor block from which
control entered the current block:

```tac
join:
  x := phi [left: x_left, right: x_right]
  goto exit
```

If execution reaches `join` from `left`, then `x` receives `x_left`; if it
reaches `join` from `right`, then `x` receives `x_right`.
