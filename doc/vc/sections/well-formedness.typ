#import "tac-code.typ": tac-code
#show raw.where(lang: "tac"): it => tac-code(it.text)

= Well-Formed Programs

The grammar admits more programs than the VC generators are meant to consume.
This section records the structural restrictions used by the two main VC
generation styles.

== CFG Vocabulary

The control-flow graph, or CFG, has one node per basic block. There is an edge
$b -> b'$ when the terminator of $b$ may transfer control to $b'$.

The successors of $b$ are the blocks $b'$ such that $b -> b'$. The predecessors
of $b$ are the blocks $p$ such that $p -> b$.

An entry-to-exit path is a CFG path that starts at the distinguished entry block
and ends at the distinguished exit block.

== SESE

A program is in single-entry single-exit form when:

- it has distinguished, distinct `entry` and `exit` blocks,
- execution starts only at `entry`,
- normal completed executions end at `exit`,
- every block lies on some entry-to-exit path.

The last condition rules out unreachable blocks and dead regions that cannot
contribute to an entry-to-exit execution.

== SSA

In static single assignment form:

- every register is assigned at most once,
- phi assignments appear as a contiguous prefix of a basic block,
- a phi assignment has one incoming value for each predecessor of its block.

SSA names merge values explicitly at join blocks:

```tac
left:
  x_left := 1
  goto join

right:
  x_right := 2
  goto join

join:
  x := phi [left: x_left, right: x_right]
  goto exit
```


== DSA

In dynamic single assignment form, definitions are classified as static or
dynamic.

A definition is static when its left-hand side is assigned once in the program.
A definition is dynamic when the same left-hand side is assigned in multiple
sibling predecessor blocks. Dynamic assignments form a contiguous suffix of the
predecessor blocks, immediately before their terminators.

The DSA version of the previous SSA example pushes the phi assignment into the
predecessors:

```tac
left:
  x_left := 1
  x := x_left
  goto join

right:
  x_right := 2
  x := x_right
  goto join

join:
  goto exit
```

Here the two assignments to `x` are dynamic definitions. They occur in sibling
predecessors of `join`, and each assignment is at the end of its block. DSA can
also be viewed as placing these assignments on the incoming edges to `join`.

== SSA and DSA Conversion

The conversion from SSA to DSA replaces each phi block:

```tac
join:
  x := phi [p1: v1, p2: v2, ...]
```

with assignments inserted at the end of the corresponding predecessor blocks:

```tac
p1:
  ...
  x := v1
  goto join

p2:
  ...
  x := v2
  goto join

join:
  ...
```

The reverse conversion collects sibling dynamic assignments into a phi node at
the successor block.

== SASA

A program is in single-assume single-assert form when:

- it is SESE,
- it has exactly one `assume` command and exactly one `assert` command,
- both commands appear in the exit block as:

```tac
exit:
  assume pre
  assert post
  halt
```

Here `pre` is any bool expression, while `post` is a bool register. There are
no other commands in the exit block.

Every program can be reduced to SASA form by accumulating assumptions into a
single precondition and assertions into a single postcondition. Informally,
`pre` is the conjunction of the assumptions required along an entry-to-exit
execution, and `post` summarizes the assertion obligations for that execution.
Earlier assumes and asserts are replaced by ordinary control/data constraints
whose effect is reflected in `pre` and `post`.

== Safety

A program is safe when every entry-to-exit execution that satisfies all assumes
also satisfies all asserts.

For a SASA program, this becomes:

#align(center)[
  $ forall "entry-to-exit executions" xi. "pre"(xi) => "post"(xi) $
]

The VC is oriented toward the negation of safety: it asks whether there exists
an entry-to-exit execution satisfying `pre` and falsifying `post`.
