#import "@preview/ctheorems:1.1.3": *
#import "@preview/codelst:2.0.2": sourcecode

#let project(
    title: "",
    authors: (),
    date: (datetime.today().year(), datetime.today().month(), datetime.today().day()),
    repo: "",
    license: "CC BY 4.0",
    body) = {
  set document(author: authors, title: title)

  set page(numbering: "1", number-align: center)

  set heading(numbering: "1.1")

  set text(size: 8pt, font: "Shippori Mincho B1", lang: "ja")

  show math.equation: set text(font: ("New Computer Modern Math", "Shippori Mincho B1"))

  show raw: set text(size: 7pt, font: ("JuliaMono", "Noto Sans JP"))

  show raw.where(block: false): box.with(
    inset: (x: 0pt, y: 0pt),
    outset: (y: 3pt),
    radius: 1pt,
  )
  
  show raw.where(block: true): block.with(
    inset: 0pt,
    radius: 1pt,
  )
  
  set raw(lang: "lean")

  show link: set text(weight: "bold", fill: gray)

  grid(
    columns: (auto, 1fr, auto),
    align: (left + horizon, center + bottom, right + top),
    rect(stroke: none, width: 220pt)[
      #block(text(weight: 700, 1.75em, title))
      #pad(
        top: .5em,
        x: 1em,
        grid(
          gutter: .6em,
          ..authors.map(author => strong(author)),
        )
      )
    ],
    stack(),
    rect(
      width: 85pt,
      fill: black,
      stroke: none,
      inset: 14pt,
      text(
        font: ("JuliaMono", "Noto Sans JP"),
        fill: white,
        size: 6pt,        
      )[
        #align(left)[repo: #link(repo, emph(repo))]
        #align(center)[\* \* \*]
        #align(center)[#strong(license)]
        #align(center)[#date.at(0)/#date.at(1)/#date.at(2)]
      ]
    ),
  )

  set par(justify: true)

  show: thmrules.with(qed-symbol: [❏])

  body

  set text(font: "libertinus serif", lang: "en")

  bibliography("references.bib", full: true)
}

#let sqthmbox(name, title, base: "heading") = thmbox(
  name,
  title,
  stroke: luma(230),
  base: base
)

#let barthmbox(name, title) = thmbox(
  name,
  title,
  stroke: (left: (thickness: 1pt, paint: luma(230))),
  inset: (left: 12pt, top: 5pt, bottom: 8pt),
  radius: 0pt
)

#let lemma = sqthmbox("lemma", "補題")

#let theorem = sqthmbox("theorem", "定理")

#let fact = sqthmbox("fact", "Fact")

#let theoremq = sqthmbox("theoremq", "定理?")

#let corollary = sqthmbox("corollary", "系", base: "theorem")

#let definition = barthmbox("definition", "定義")

#let notation = barthmbox("notation", "記法")

#let remark = barthmbox("remark", "Remark")

#let example = barthmbox("example", "例")

#let proof = thmproof("proof", "Proof")

#let struct(body) = {
  rect(
    width: 100%,
    stroke: (left: (thickness: 1pt, paint: luma(230))),
    inset: (left: 12pt, top: 5pt, bottom: 8pt))[#body]
  }

#let code = sourcecode.with(
  numbers-start: 40,
  gutter: 1em,
  frame: block.with(
    radius: 0pt,
    fill: luma(250),
    stroke: (left: 1pt + luma(20)),
    inset: (x: 1.5em, y: 1em),
  ),
)

#let dand = $⩕$
#let dor = $⩖$

#let brak(..args) = {
  let a = args.pos().join(", ")
  $lr(angle.l #a angle.r)$
  }

#let size(x) = $lr(| #x |)$

#let proves = $tack.r$
#let nproves = $tack.r.not$

#let Nat = $NN$
#let Rat = $QQ$
#let Real = $RR$