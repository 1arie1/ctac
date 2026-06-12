#let tac-keywords = (
  "assume",
  "assert",
  "else",
  "false",
  "goto",
  "halt",
  "havoc",
  "if",
  "not",
  "phi",
  "true",
)

#let tac-keyword-color = rgb("#7c3aed")
#let tac-label-color = rgb("#0369a1")
#let tac-op-color = rgb("#475569")

#let tac-token(tok) = {
  if tac-keywords.contains(tok) {
    text(fill: tac-keyword-color, weight: "semibold")[#tok]
  } else if tok.ends-with(":") {
    text(fill: tac-label-color, weight: "semibold")[#tok]
  } else if tok == ":=" or tok == "==" or tok == "<=" or tok == ">=" or tok == "<" or tok == ">" {
    text(fill: tac-op-color, weight: "semibold")[#tok]
  } else {
    tok
  }
}

#let tac-line(line) = {
  if line.trim() == "" {
    linebreak()
  } else {
    let indent = if line.starts-with("  ") { h(1.2em) } else { none }
    let body = if line.starts-with("  ") { line.slice(2) } else { line }
    indent
    for tok in body.split(" ") {
      tac-token(tok)
      " "
    }
    linebreak()
  }
}

#let tac-code(src) = {
  block(
    fill: rgb("#f8fafc"),
    stroke: 0.6pt + rgb("#dbe3ee"),
    radius: 3pt,
    inset: (x: 9pt, y: 7pt),
    width: 100%,
  )[
    #set text(font: "Menlo", size: 9pt)
    #for line in src.split("\n") {
      tac-line(line)
    }
  ]
}

#let logic-box(body) = {
  block(
    fill: rgb("#f7fbff"),
    stroke: 0.6pt + rgb("#cfe3f7"),
    radius: 3pt,
    inset: (x: 10pt, y: 8pt),
    width: 100%,
  )[
    #set align(left)
    #set math.equation(number-align: left)
    #body
  ]
}
