= Overview

This document describes the foundations of verification-condition generation
for ctac.

The purpose is not to mirror the current implementation module-by-module.
Instead, the goal is to define the mathematical objects, semantic conventions,
and proof obligations that a VC generator for TAC should satisfy. The
implementation can then be evaluated against this foundation, and future
encoder variants can share the same vocabulary.

== Scope

We start with loop-free TAC programs that have a distinguished entry block and
a single assertion site. Multi-assert programs are treated as a preprocessing
problem: they may be transformed into an equivalent single-assert program
before VC generation.

At this level, a VC generator consumes:

- a control-flow graph of basic blocks,
- commands inside each block,
- a symbol table and sort information,
- TAC expressions over scalars and maps,
- the assertion whose failure reachability is being queried.

It produces an SMT formula whose satisfiability answers the assertion-failure
question:

$ "sat"("VC"(P, A)) <=> "there exists an execution of P reaching a failure of A" $

Thus, an unsatisfiable VC means the assertion is proved for the encoded
program semantics.

== Main Questions

The foundational presentation should answer these questions:

- What is the TAC program model used by VC generation?
- What does it mean for a block or command to be reachable?
- How are assignments, havoc, assume, branch, and assert commands interpreted?
- How are path conditions represented?
- How are scalar expressions lowered to SMT?
- How are bytemaps and other map-like values modeled?
- Which side conditions are required before VC generation?
- Which transformations are semantic preprocessing, and which are encoding
  choices?

== Document Plan

The intended structure is:

1. Program model: blocks, commands, symbols, expressions, and control flow.
2. Operational intuition: executions, feasibility, and assertion failure.
3. VC shape: reachability variables, command constraints, and failure query.
4. Expression semantics: arithmetic, bit-vector-like integer domains, and
   uninterpreted operations.
5. Map semantics: reads, writes, and finite update chains.
6. Preconditions and preprocessing: acyclicity, single assertion, critical
   edges, and well-formed definitions.
7. Soundness statement: what it means for the generated VC to be sound with
   respect to TAC executions.

== Conventions

We use $P$ for a TAC program, $B$ for the set of basic blocks, and $"entry"$ for
the entry block. A block $b in B$ has a sequence of commands and zero or more
successor blocks. Reachability of a block is represented abstractly by a
Boolean predicate $R_b$.

When we write $"VC"(P, A)$, $A$ denotes the selected assertion site. The VC is
oriented toward bug finding: satisfiable means an assertion-failure execution
exists, and unsatisfiable means no such execution exists under the modeled
semantics.
