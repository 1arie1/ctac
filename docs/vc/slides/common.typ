#import "../sections/tac-code.typ": tac-code, logic-box, tac-label-color
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let muted = rgb("#475569")
#let accent = rgb("#0369a1")

#let two-col(left, right, columns: (1fr, 1fr)) = grid(
  columns: columns,
  gutter: 0.7cm,
  left,
  right,
)

#let three-col(a, b, c) = grid(
  columns: (1fr, 1fr, 1fr),
  gutter: 0.45cm,
  a,
  b,
  c,
)

#let formula-part(body) = text(fill: accent, weight: "semibold")[#body]

#let compact-list(body) = {
  set text(size: 16pt)
  body
}

// Question prompt for puzzle-style slides.
#let question-box(body) = block(
  fill: rgb("#fffbeb"),
  stroke: 0.8pt + rgb("#f59e0b"),
  radius: 3pt,
  inset: (x: 10pt, y: 8pt),
  width: 100%,
)[#body]

// Terminal output for live-tool slides.
#let term-box(body) = block(
  fill: rgb("#0f172a"),
  radius: 4pt,
  inset: (x: 12pt, y: 10pt),
  width: 100%,
)[
  #set text(font: "Menlo", size: 12.5pt, fill: rgb("#cbd5e1"))
  #set par(leading: 0.45em)
  #body
]

#let sh(s) = {
  text(fill: rgb("#4ade80"), weight: "semibold")[\$ ]
  text(fill: rgb("#f1f5f9"))[#s]
  linebreak()
}
#let out(s) = { text(fill: rgb("#94a3b8"))[#s]; linebreak() }
#let hi(s) = { text(fill: rgb("#fbbf24"), weight: "semibold")[#s]; linebreak() }

#let sat-chip = box(
  fill: rgb("#fee2e2"), stroke: 0.7pt + rgb("#dc2626"), radius: 2.5pt,
  inset: (x: 6pt, y: 2.5pt),
  text(fill: rgb("#b91c1c"), weight: "bold", size: 15pt)[SAT],
)
#let unsat-chip = box(
  fill: rgb("#dcfce7"), stroke: 0.7pt + rgb("#16a34a"), radius: 2.5pt,
  inset: (x: 6pt, y: 2.5pt),
  text(fill: rgb("#15803d"), weight: "bold", size: 15pt)[UNSAT],
)

// ---------------------------------------------------------------------------
// The running diamond as a CFG picture.
//
// Every encoder deck reuses this figure so the audience sees the same graph
// encoded three ways. Each node shows the block name, optionally its
// commands (code:), and optionally a per-node annotation (note:) rendered in
// the accent color -- that is where a deck attaches its formula pieces.
// Edge labels (t-label / f-label / lj-label / rj-label / je-label) carry
// edge-attached constraints such as JUMPS or PHI.
// ---------------------------------------------------------------------------

#let cfg-blk(name, code: none, note: none, name-size: 15pt, code-size: 11pt, note-size: 12.5pt) = {
  set align(center)
  stack(
    spacing: 4.5pt,
    text(fill: tac-label-color, weight: "semibold", size: name-size)[#name],
    ..if code != none {
      (text(font: "Menlo", size: code-size, fill: rgb("#1e293b"))[#code],)
    } else { () },
    ..if note != none {
      (text(fill: accent, size: note-size, weight: "medium")[#note],)
    } else { () },
  )
}

#let diamond-cfg(
  entry-code: none, left-code: none, right-code: none, join-code: none, exit-code: none,
  entry-note: none, left-note: none, right-note: none, join-note: none, exit-note: none,
  t-label: none, f-label: none, lj-label: none, rj-label: none, je-label: none,
  node-inset: 7pt,
  label-size: 13pt,
) = {
  let n(pos, name, code, note) = node(
    pos,
    cfg-blk(name, code: code, note: note),
    fill: rgb("#f8fafc"),
    stroke: 0.8pt + rgb("#64748b"),
    shape: fletcher.shapes.rect,
    corner-radius: 4pt,
    inset: node-inset,
  )
  let lbl(body) = if body == none { none } else {
    text(size: label-size, fill: muted, weight: "medium")[#body]
  }
  set align(center)
  diagram(
    spacing: (18pt, 16pt),
    n((0, 0), "entry", entry-code, entry-note),
    n((1, -0.75), "left", left-code, left-note),
    n((1, 0.75), "right", right-code, right-note),
    n((2, 0), "join", join-code, join-note),
    n((3, 0), "exit", exit-code, exit-note),
    edge((0, 0), (1, -0.75), "-|>", lbl(t-label), label-side: left),
    edge((0, 0), (1, 0.75), "-|>", lbl(f-label), label-side: right),
    edge((1, -0.75), (2, 0), "-|>", lbl(lj-label), label-side: left),
    edge((1, 0.75), (2, 0), "-|>", lbl(rj-label), label-side: right),
    edge((2, 0), (3, 0), "-|>", lbl(je-label), label-side: left),
  )
}

// The diamond with its program text inside the nodes (the default view).
#let diamond-cfg-full(
  entry-note: none, left-note: none, right-note: none, join-note: none, exit-note: none,
  t-label: none, f-label: none, lj-label: none, rj-label: none, je-label: none,
  phi-style: "phi",  // "phi" | "dsa" | "ite"
) = {
  let left-code = if phi-style == "dsa" {
    [a_left := x + 1\ a := a_left]
  } else { [a_left := x + 1] }
  let right-code = if phi-style == "dsa" {
    [a_right := y + 1\ a := a_right]
  } else { [a_right := y + 1] }
  let join-code = if phi-style == "phi" {
    [a := phi [left: a_left,\ #h(2.6em) right: a_right]\ ok := a > 0]
  } else if phi-style == "ite" {
    [a := ite(c, a_left, a_right)\ ok := a > 0]
  } else {
    [ok := a > 0]
  }
  diamond-cfg(
    entry-code: [x := havoc\ y := havoc\ c := x \< y],
    left-code: left-code,
    right-code: right-code,
    join-code: join-code,
    exit-code: [assume true\ assert ok\ halt],
    entry-note: entry-note, left-note: left-note, right-note: right-note,
    join-note: join-note, exit-note: exit-note,
    t-label: t-label, f-label: f-label,
    lj-label: lj-label, rj-label: rj-label, je-label: je-label,
  )
}
