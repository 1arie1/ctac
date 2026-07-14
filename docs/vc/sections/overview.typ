= Overview

This document presents verification-condition generation for ctac through a
small explanatory language and three VC generation algorithms.

The purpose is not to mirror the current implementation module-by-module.
Instead, the goal is to define a common program model and use it to explain how
different encodings represent control flow, data flow, and assertion failure.
The presentation also identifies the program forms and soundness conditions on
which those encodings rely.

The small language used in this document is *Tiny TAC*, abbreviated `ttac`.
It is a TAC-like core language for explaining VC generation, not a complete
description of the implementation input format.

== Scope

We start with loop-free `ttac` programs in single-entry single-exit (SESE) form.
The core VCGen problem uses single-assume single-assert (SASA) form: the
distinguished exit block contains one accumulated assumption and one purified
assertion. Programs with assumptions or assertions elsewhere are reduced to
this form before the core encodings are applied.

At this level, a VC generator consumes:

- a control-flow graph of basic blocks,
- commands inside each block,
- a symbol table and sort information,
- `ttac` expressions over scalars and maps,
- an exit assumption and assertion whose failure is being queried.

It produces an SMT formula whose satisfiability answers the assertion-failure
question:

$ "sat"("VCGen"(P)) <=> "P has an unsafe entry-to-exit execution" $

Thus, an unsatisfiable VC means the assertion is proved for the encoded
program semantics.

== Main Questions

The foundational presentation should answer these questions:

- What is the `ttac` program model used by VC generation?
- Which well-formed program representations do the encodings require?
- How are assignments, havoc, assume, branch, and assert commands interpreted?
- How do explicit reachability, weakest-precondition equations, and gated SSA
  represent the same path semantics?
- Which optimizations and side conditions preserve soundness?
- How can references and borrows be compiled into the core language using
  prophecy-style values?

== Document Plan

The document is organized as follows:

1. *Syntax and semantics* defines Tiny TAC types, expressions, bytemaps,
   commands, basic blocks, and executions.
2. *Well-formed programs* defines SESE, SSA, DSA, and SASA, and states the
   safety query used by VC generation.
3. *VC generation algorithms* develops three encodings of that query:
   SeaHorn-style explicit block reachability, Boogie-style backward block
   equations, and SeaBMC-style gated SSA. It also discusses encoding variants,
   soundness pitfalls, Thin GSSA, and cone-of-influence reduction.
4. *References and borrowing* extends Tiny TAC with constant and mutable
   references, then compiles them back to the core language using reference
   triples and prophecy-style promises.

== Conventions

We use $P$ for a `ttac` program, $B$ for the set of basic blocks, and
$"entry"$ and $"exit"$ for its distinguished entry and exit blocks. A block
$b in B$ has a sequence of commands followed by a terminator. Where an encoding
uses explicit block reachability, it writes the Boolean variable $bb_b$.

When we write $"VCGen"(P)$, $P$ is understood to satisfy the program-form
requirements of the algorithm under discussion. The formula is oriented toward
bug finding: satisfiable means an unsafe execution exists, and unsatisfiable
means no such execution exists under the modeled semantics.
