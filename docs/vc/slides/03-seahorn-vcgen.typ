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
  #text(size: 28pt)[SeaHorn Style]
]

== Idea

SeaHorn-style VCGen keeps control flow explicit.

#v(0.2cm)

For each block `i`, introduce a Boolean reachability variable:

#align(center)[
  $ bb_i $
]

Then constrain the selected blocks so they describe an entry-to-exit path.

#v(0.3cm)

#logic-box[
  $
    "VCGen_SeaHorn"(P) =
      #formula-part[CFG] and
      #formula-part[DEF] and
      #formula-part[JUMPS] and
      #formula-part[PHI] and
      #formula-part[ERROR]
  $
]

#compact-list[
- `CFG`: selected block variables form a path.
- `DEF`: assignments hold when their block is selected.
- `JUMPS`: selected branch edges satisfy branch conditions.
- `PHI`: selected incoming edges choose phi values.
- `ERROR`: the selected exit violates the assertion.
]

== The Diamond, Encoded On The Picture

Each component lives somewhere on the graph:

#alternatives[
  #diamond-cfg(
    entry-note: [$bb_"entry"$ #text(size: 11pt, fill: muted)[(required)]],
    left-note: $bb_"left" => bb_"entry"$,
    right-note: $bb_"right" => bb_"entry"$,
    join-note: $bb_"join" => bb_"left" or bb_"right"$,
    exit-note: [$bb_"exit" => bb_"join"$ #text(size: 11pt, fill: muted)[(also required)]],
  )
  #align(center)[#formula-part[CFG] — every selected block has a selected
  predecessor; `entry` and `exit` are forced.]
][
  #diamond-cfg(
    entry-note: $bb_"entry" => c = (x < y)$,
    left-note: $bb_"left" => a_"left" = x + 1$,
    right-note: $bb_"right" => a_"right" = y + 1$,
    join-note: $bb_"join" => "ok" = (a > 0)$,
    exit-note: text(size: 11pt, fill: muted)[no static defs],
  )
  #align(center)[#formula-part[DEF] — assignments become equalities,
  guarded by their block. Havoc contributes nothing.]
][
  #diamond-cfg(
    t-label: $(bb_"entry" and bb_"left") => c$,
    f-label: $(bb_"entry" and bb_"right") => not c$,
    label-size: 12pt,
  )
  #align(center)[#formula-part[JUMPS] — branch conditions attach to the
  *edges* of the conditional terminator.]
][
  #diamond-cfg(
    lj-label: $(bb_"left" and bb_"join") => a = a_"left"$,
    rj-label: $(bb_"right" and bb_"join") => a = a_"right"$,
    label-size: 12pt,
  )
  #align(center)[#formula-part[PHI] — the selected incoming edge chooses
  the phi value. (The DSA idea, expressed on edges.)]
][
  #diamond-cfg(
    exit-note: $bb_"exit" => "true" and not "ok"$,
  )
  #align(center)[#formula-part[ERROR] — the selected exit must satisfy
  `pre` and falsify `post`. With $bb_"exit"$ forced, a model is a complete
  failing execution.]
]

== The Whole Formula

#logic-box[
  #set text(size: 15pt)
  $
    #formula-part[CFG] &= bb_"entry"
      and (bb_"left" => bb_"entry")
      and (bb_"right" => bb_"entry") \
      &quad and (bb_"join" => bb_"left" or bb_"right")
      and (bb_"exit" => bb_"join")
      and bb_"exit" \
    #formula-part[DEF] &=
      (bb_"entry" => c = (x < y))
      and (bb_"left" => a_"left" = x + 1) \
      &quad and (bb_"right" => a_"right" = y + 1)
      and (bb_"join" => "ok" = (a > 0)) \
    #formula-part[JUMPS] &=
      ((bb_"entry" and bb_"left") => c)
      and ((bb_"entry" and bb_"right") => not c) \
    #formula-part[PHI] &=
      ((bb_"left" and bb_"join") => a = a_"left")
      and ((bb_"right" and bb_"join") => a = a_"right") \
    #formula-part[ERROR] &= bb_"exit" => top and not "ok"
  $
]

#v(0.25cm)
A satisfying model is a candidate unsafe execution: a selected
entry-to-exit path, consistent assignments and edge conditions, and a
false assertion at `exit`.

== Optimization: Unguarded DEF

Static definitions may be exposed as top-level equations:

#two-col[
  Guarded:

  #logic-box[
    $ bb_i => x = y + 1 $
  ]
][
  Unguarded:

  #logic-box[
    $ x = y + 1 $
  ]
]

#pause
#v(0.2cm)

Why bother? Top-level equalities feed algebraic simplification:

#logic-box[
  $ x = y + 1 and z = x + 2 quad arrow.r.double.long quad z = y + 3 $
]

Sound only when the definition and its side conditions are globally safe —
*keep that clause in mind for the pitfalls.*

== Optimization: Phi As ITE

#two-col[
  Edge implications:

  #logic-box[
    $
      (bb_i and bb_j) => x = x_i \
      (bb_k and bb_j) => x = x_k
    $
  ]
][
  One defining equation:

  #logic-box[
    $ x = "ite"(bb_i, x_i, x_k) $
  ]
]

After Boolean propagation learns $bb_i$, the ITE collapses to $x = x_i$.

#v(0.2cm)
#text(fill: muted, size: 16pt)[The ITE form gives the merge a syntactic
definition the solver can substitute — at a price we will meet in
pitfall 2.]

== The Optimized Diamond

Same program — forward CFG, unguarded DEF, phi as ITE:

#logic-box[
  #set text(size: 15pt)
  $
    #formula-part[CFG] &= bb_"entry"
      and (bb_"entry" => bb_"left" or bb_"right")
      and (bb_"left" => bb_"join") \
      &quad and (bb_"right" => bb_"join")
      and (bb_"join" => bb_"exit")
      and bb_"exit" \
    #formula-part[DEF] &=
      c = (x < y)
      and a_"left" = x + 1
      and a_"right" = y + 1 \
      &quad and a = "ite"(bb_"left", a_"left", a_"right")
      and "ok" = (a > 0) \
    #formula-part[JUMPS] &=
      ((bb_"entry" and bb_"left") => c)
      and ((bb_"entry" and bb_"right") => not c) \
    #formula-part[PHI] &= top \
    #formula-part[ERROR] &= bb_"exit" => top and not "ok"
  $
]

#v(0.2cm)
Reachability flows forward; definitions are naked equations ready for
substitution; the phi component is *empty* — the merge lives in `DEF`
as an ITE.

== Pitfall 1: A Critical Edge

#two-col(columns: (1.05fr, 1fr))[
  ```tac
  entry:
    c := havoc
    if c goto join else mid

  mid:
    goto join

  join:
    ok := phi [entry: true, mid: false]
  ```
][
  The encoder emits the true-edge condition:

  #logic-box[
    $ (bb_"entry" and bb_"join") => c $
  ]

  #question-box[
    The program is unsafe (take the `mid` path). Does the encoder
    find the bug?
  ]
]

#pause
*No.* On `entry -> mid -> join`, both $bb_"entry"$ and $bb_"join"$ are
true while $c$ is false — the constraint *rejects the real bug path*.
Block variables cannot tell which incoming edge was taken.

== Pitfall 1: The Repair — Split The Edge

An edge $u -> v$ is critical when $|"succ"(u)| > 1 and |"pred"(v)| > 1$:

#align(center)[#image("../sections/critical-edge.svg", width: 34%)]

#two-col[
  Insert a landing block:

  ```tac
  entry:
    c := havoc
    if c goto e2j else mid
  e2j:
    goto join
  ```
][
  The condition attaches to a non-critical edge:

  #logic-box[
    $ (bb_"entry" and bb_"e2j") => c $
  ]

  $bb_"e2j"$ is true *only* on the true edge.
]

== Pitfall 2: A Safe Program Goes SAT

#two-col(columns: (1.1fr, 1fr))[
  ```tac
  left:
    x_left := true
    p_left := true
    goto join

  right:
    x_right := false
    p_right := false
    goto join

  join:
    x := phi [left: x_left, right: x_right]
    p := phi [left: p_left, right: p_right]
    ok := x == p
  ```
][
  Safe: both paths make `x` and `p` equal.

  The two phis are emitted as independent ITEs, cases in different
  orders:

  #logic-box[
    #set text(size: 15pt)
    $
      x = "ite"(bb_"left", x_"left", x_"right") \
      p = "ite"(bb_"right", p_"right", p_"left")
    $
  ]

  #question-box[
    The solver reports SAT. What model did it find?
  ]
]

#pause
$bb_"left" = bb_"right" = "true"$: the first ITE reads the *left* value,
the second reads the *right* value — $x = "true", p = "false"$. A mixed
state no execution produces: a *spurious counterexample*.

== Pitfall 2: The Repair — Predecessor Exclusivity

With edge implications, selecting both predecessors is an immediate
contradiction ($x = x_"left"$ and $x = x_"right"$ conflict).

An ITE merge has only *one* equality — it silently picks an arm.

#v(0.25cm)

The repair is an at-most-one constraint at the merge:

#logic-box[
  $ not (bb_"left" and bb_"right") $
]

#v(0.25cm)

Equivalently: any CFG encoding with edge variables must enforce that at
most one incoming edge to a merge fires.

#v(0.2cm)
#text(fill: muted, size: 16pt)[Phi-as-ITE trades a built-in exclusivity
check for solver-friendliness — the side condition must come back
explicitly.]

== Pitfall 3: An Unguarded Path-Local Fact

`narrow64` is identity, but its encoding adds a 64-bit range fact for
its result:

#two-col(columns: (1.1fr, 1fr))[
  ```tac
  entry:
    x := havoc
    small := x < 2^64
    if small goto narrow_block else exit

  narrow_block:
    y := narrow64(x)
    goto exit

  exit:
    assume not small
    assert false
    halt
  ```
][
  Unsafe: pick $x >= 2^64$, skip `narrow_block`, reach
  `assert false`.

  The encoder emits the definition *unguarded*:

  #logic-box[
    #set text(size: 15pt)
    $ y = x and 0 <= y and y <= 2^64 - 1 $
  ]

  #question-box[
    Does the solver find the bug?
  ]
]

#pause
*No — UNSAT.* The global range fact bounds $x$ on *every* path; the
failing path needs $x >= 2^64$ and is now inconsistent. A fact from an
unvisited block killed a real bug.

== Pitfall 3: The Repair — Guard Path-Local Facts

Keep the range fact local to its block:

#logic-box[
  $ bb_"narrow_block" => (y = x and 0 <= y and y <= 2^64 - 1) $
]

#v(0.3cm)

The unguarded-DEF optimization is safe for *total* right-hand sides.
It breaks the moment the definition smuggles in a *path-local axiom* —
a range fact, a partial-operation side condition, an operator axiom
valid only where the call appears.

#v(0.2cm)

Guard such facts by their triggering block, or prove them globally safe.

== The Two Ways To Be Wrong

#{
  set text(size: 16pt)
  table(
    columns: (auto, 1fr, 1fr),
    stroke: 0.5pt + rgb("#cbd5e1"),
    inset: 8pt,
    table.header([*Pitfall*], [*Effect*], [*Failure mode*]),
    [critical edges], [*missing paths* — a real execution is ruled out],
      [bug silently missed],
    [ITE merge without exclusivity], [*infeasible paths* — the formula
      admits states no execution produces], [spurious counterexample],
    [unguarded path-local facts], [*missing paths* — facts from an
      unvisited block constrain the failing path], [bug silently missed],
  )
}

#v(0.3cm)

Missing paths make the encoder *unsound toward silence*; infeasible
paths make it *unsound toward noise*. Every encoding change should be
audited against both directions.
