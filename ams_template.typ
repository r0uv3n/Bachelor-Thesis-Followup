#let script-size = 7.97224pt
#let footnote-size = 8.50012pt
#let small-size = 9.24994pt
#let normal-size = 10.00002pt
#let large-size = 11.74988pt

// This function gets your whole document as its `body` and formats
// it as an article in the style of the American Mathematical Society.
#let ams-article(
  // The article's title.
  title: [Paper title],

  // An array of authors. For each author you can specify a name,
  // department, organization, location, and email. Everything but
  // but the name is optional.
  authors: (),

  // Your article's abstract. Can be omitted if you don't have one.
  abstract: none,

  // The article's paper size. Also affects the margins.
  paper-size: "us-letter",

  // The path to a bibliography file if you want to cite some external
  // works.
  bibliography-file: none,

  // The document's content.
  body,
) = {
  // Formats the author's names in a list with commas and a
  // final "and".
  let names = authors.map(author => author.name)
  let author-string = if authors.len() == 2 {
    names.join(" and ")
  } else {
    names.join(", ", last: ", and ")
  }

  // Set document metadata.
  set document(title: title, author: names)

  // Set the body font. AMS uses the LaTeX font.
  set text(size: normal-size, font: "New Computer Modern")

  // Configure the page.
  set page(
    paper: paper-size,

    // The page header should show the page number and list of
    // authors, except on the first page. The page number is on
    // the left for even pages and on the right for odd pages.
    header-ascent: 14pt,
    header: locate(loc => {
      let i = counter(page).at(loc).first()
      if i == 1 { return }
      set text(size: script-size)
      grid(
        columns: (6em, 1fr, 6em),
        if calc.even(i) [#i],
        align(center, upper(
          if calc.odd(i) { title } else { author-string }
        )),
        if calc.odd(i) { align(right)[#i] }
      )
    }),

    // On the first page, the footer should contain the page number.
    footer-descent: 12pt,
    footer: locate(loc => {
      let i = counter(page).at(loc).first()
      if i == 1 {
        align(center, text(size: script-size, [#i]))
      }
    })
  )


  // Display the title and authors.
  v(35pt, weak: true)
  align(center, upper({
    text(size: large-size, weight: 700, title)
    v(25pt, weak: true)
    text(size: footnote-size, author-string)
  }))

  // Configure paragraph properties.
  set par(first-line-indent: 1.2em, justify: true, leading: 0.58em)
  show par: set block(spacing: 0.58em)

  // Display the abstract
  if abstract != none {
    v(20pt, weak: true)
    set text(script-size)
    show: pad.with(x: 35pt)
    smallcaps[Abstract. ]
    abstract
  }

  // Display the article's contents.
  v(29pt, weak: true)
  body

  // Display the bibliography, if any is given.
  if bibliography-file != none {
    show bibliography: set text(8.5pt)
    show bibliography: pad.with(x: 0.5pt)
    bibliography(bibliography-file)
  }

  // The thing ends with details about the authors.
  show: pad.with(x: 11.5pt)
  set par(first-line-indent: 0pt)
  set text(7.97224pt)

  for author in authors {
    let keys = ("department", "organization", "location")

    let dept-str = keys
      .filter(key => key in author)
      .map(key => author.at(key))
      .join(", ")

    smallcaps(dept-str)
    linebreak()

    if "email" in author [
      _Email address:_ #link("mailto:" + author.email) \
    ]

    if "url" in author [
      _URL:_ #link(author.url)
    ]

    v(12pt, weak: true)
  }
}

// // The ASM template also provides a theorem function.
// #let theorem(body, numbered: true) = figure(
//   body,
//   kind: "theorem",
//   supplement: [Theorem],
//   numbering: if numbered { "1" },
// )

// // And a function for a proof.
// #let proof(body) = block(spacing: 11.5pt, {
//   emph[Proof.]
//   [ ] + body
//   h(1fr)
//   box(scale(160%, origin: bottom + right, sym.square.stroked))
// })