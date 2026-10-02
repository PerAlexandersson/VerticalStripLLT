# Manuscript

`llt-flip-classes.tex` is the source and `llt-flip-classes.pdf` the current
build, kept in the repository for easy viewing. Sections are in `sections/`,
the diagram macros in `diagrams.tex`, and the bibliography in
`references.bib`. Build outside the Dropbox checkout and copy the PDF back:

```bash
latexmk -pdf -outdir=<build-dir> llt-flip-classes.tex
cp <build-dir>/llt-flip-classes.pdf .
```
