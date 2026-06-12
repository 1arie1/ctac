= VC Generation Algorithms

*VCGen Problem.* Given a program $P$ in SASA form, $"VCGen"(P)$ is a formula
$Phi$ such that $Phi$ is satisfiable iff $P$ is unsafe.

For a SASA program, this can be read as an execution query:

#align(center)[
  $ exists xi. "Path"(xi) and "pre"(xi) and not "post"(xi) $
]

Here $xi$ ranges over entry-to-exit executions. The predicate $"Path"$ captures
the program semantics: control flow, assignments, havoc choices, map updates,
and branch decisions. The query is satisfiable exactly when there is an
execution that satisfies the accumulated precondition and falsifies the final
assertion condition.

Different VC generation algorithms choose different ways to represent
$"Path"$. We consider three styles:

- $"VCGen_SeaHorn"$: explicit control representation via block variables with
  side-conditions, naturally in SSA.
- $"VCGen_Boogie"$: weakest-precondition style formulas, naturally over DSA.
- $"VCGen_SeaBMC"$: data-flow driven with control compiled into control.

The algorithms should be compared by the shape of the formula they generate,
the program form they prefer, and the solver behavior they induce.

#include "seahorn-vcgen.typ"
