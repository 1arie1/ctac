#set document(
  title: "ctac VC Generation",
  author: "ctac contributors",
)

#set page(
  paper: "us-letter",
  margin: (x: 1in, y: 1in),
)

#set text(
  font: "Libertinus Serif",
  size: 11pt,
)

#set heading(numbering: "1.1")
#show heading: set block(above: 1.2em, below: 0.6em)
#show heading.where(level: 4): set heading(numbering: none)

#align(center)[
  #text(size: 18pt, weight: "bold")[VC Generation] \
  #text(size: 11pt)[Arie Gurfinkel]
]

#outline(title: "Contents")

#include "sections/overview.typ"
#include "sections/syntax-semantics.typ"
#include "sections/well-formedness.typ"
#include "sections/vcgen-algorithms.typ"
#include "sections/references-borrowing.typ"
