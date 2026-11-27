# Build the manuscript

**Author** The Blank Beyond  
**Version** 27 November 2026 (revised)

Use TeX Live or another LaTeX distribution providing pdfLaTeX, BibTeX, AMS classes and packages, mathtools, Latin Modern, microtype, booktabs, PGF/TikZ, hyperref, xurl, cleveref, and latexmk.

From this directory, run the build in a disposable environment with no credentials or personal files.

~~~sh
latexmk -norc -pdf -pdflatex='pdflatex -no-shell-escape %O %S' \
  -interaction=nonstopmode -halt-on-error -file-line-error main.tex
~~~

The output is main.pdf. All mathematical sections, appendices, and vector figure sources are included. No shell escape, external figure generation, or Lean build is required. The paper uses the accompanying Lean supplement for independent verification, which is built separately.

For a fixed creation timestamp, use SOURCE_DATE_EPOCH=1795737600 and FORCE_SOURCE_DATE=1. A byte-identical PDF also depends on the TeX distribution, package versions and fonts.
