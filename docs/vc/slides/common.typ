#import "../sections/tac-code.typ": tac-code, logic-box

#let muted = rgb("#475569")
#let accent = rgb("#0369a1")

#let two-col(left, right) = grid(
  columns: (1fr, 1fr),
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
