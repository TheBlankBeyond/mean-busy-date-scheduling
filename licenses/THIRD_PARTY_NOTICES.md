# Third-party notices

## Mathematical references and benchmark

Maurice Queyranne supplied the three-job data and optimal schedule in *Parallel Machines Scheduling to Preemptively Minimize the Weighted Sum of Mean Busy Dates* (2010), p. 16, discussion 2. The manuscript and `lean/TBB/BenchmarkData.lean` use those data with rational endpoints. The new checker, certificate witnesses, and proofs are identified separately from the source problem and schedule. The note is cited here and in the bibliography. Its publisher lists CC BY 4.0. The distribution includes no copy of the original note, graph, or typeset passage. [Source note](https://doi.org/10.4230/DagSemProc.10071.3)

The research credits Robert McNaughton for preemptive row wrapping and the cited literature for prior mathematics and theorems used. The vector diagrams are drawn from the mathematical construction and example data in the manuscript's own TikZ sources. [McNaughton, 1959](https://doi.org/10.1287/mnsc.6.1.1)

## Embedded typography

The PDF uses Latin Modern, copyright 2003–2021 by B. Jackowski and J. M. Nowacki on behalf of TeX Users Groups, under the GUST Font License referencing LPPL 1.3c or later. The PDF also embeds AMSFonts symbols MSAM10 and MSBM10, copyright 1997 and 2009 American Mathematical Society, under SIL Open Font License 1.1. The fonts retain their upstream terms. The package includes the applicable notices and license texts. [Latin Modern](https://ctan.org/pkg/lm) · [AMSFonts](https://ctan.org/pkg/amsfonts) · [GUST Font License](GUST-FONT-LICENSE.txt) · [LPPL](LPPL-1.3c.txt) · [AMSFonts notice and OFL](AMSFonts-OFL-1.1.txt)

## Fetched build dependencies

Lean, Mathlib, plausible, LeanSearchClient, importGraph, ProofWidgets, Aesop, Qq and Batteries use Apache-2.0 at the reviewed versions. The Lean CLI library listed as `Cli` uses MIT. Their checkouts, binaries, caches, and built-in proof checkers are obtained separately under upstream terms. `lean/lean-toolchain` and `lean/lake-manifest.json` identify the exact versions and sources. [Lean project notices](../lean/NOTICE.md)
