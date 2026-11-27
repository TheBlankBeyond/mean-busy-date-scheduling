# The Blank Beyond

## The Mathematics of Perfect Timing

**Mathematics · Original research · Preliminary finding**

An exact algorithm addressing a mathematical scheduling question posed in 2010.

### The paper

[**Exact Polynomial-Time Optimization of Weighted Mean Busy Dates on Identical Parallel Machines**](paper/manuscript.pdf)  
The Blank Beyond · revised manuscript, 27 November 2026

A job's *mean busy date* is the average time at which it is processed. The problem is to choose when jobs run so that the weighted sum of their mean busy dates is as small as possible. Jobs may pause and move between identical machines. Each job can use at most one machine at a time.

- **Theorem Q** gives a deterministic exact algorithm with weakly polynomial Turing bit complexity for rational inputs, with the number of machines part of the input. It returns a rational schedule that is globally optimal over feasible measurable schedules on the nonnegative time axis. The paper proves the algorithm, including its bit complexity, conventionally.
- **Theorem R** gives an explicit reflected construction that realizes the fractional allocation as a schedule while preserving every job's workload and first moment. It ensures machine and job nonoverlap and bounds the operations and machines used.

The question was posed by Maurice Queyranne in 2010. Earlier continuous linear programming and purification results overlap with parts of the framework. Our review identified no published result with the same full worst-case polynomial bit-time guarantee for variable machine count. Queyranne's unpublished July 2010 notes were unavailable, and scholarly priority remains unresolved. [Queyranne's proceedings note](https://doi.org/10.4230/DagSemProc.10071.3)

### Verification and reproduction

Lean proves reflected realization and the soundness of an exact rational certificate checker over the unrestricted measurable comparison class. The pinned Lean 4.36.0 environment and independent proof checkers accepted all 52 audited declarations and their exported dependencies. The typed public benchmark has exact optimum `879/40`, established through kernel-checked certificate acceptance and soundness. The full optimizer and its bit-complexity analysis use a conventional mathematical proof.

The paper reports additional executable checks performed on a private corpus. Those runs evaluated fixture data through the checker. The public repository supplies the benchmark and instructions to build, recheck the proofs, and evaluate reader-supplied certificates.

- [Build the LaTeX manuscript](paper/BUILD.md)
- [Build Lean and run independent kernel checks](lean/README.md)
- [Verify the benchmark and inspect the proof map](verification/README.md)

### Citation and licenses

> The Blank Beyond. *Exact Polynomial-Time Optimization of Weighted Mean Busy Dates on Identical Parallel Machines*. Independent research manuscript, revision 2, 27 November 2026.

[Citation metadata](CITATION.cff) · [BibTeX](CITATION.bib) · [Licensing by file type](LICENSE.md)

AI systems contributed to mathematical investigation, proof development, computational checks, Lean formalization, and manuscript preparation. A separate AI review examined the proof and reproduced scoped verification. The manuscript has yet to undergo independent human academic peer review. Specialist scrutiny of the statements, complexity proof, and formal verification scope is welcome.

The Blank Beyond is an independent science, technology and discovery company advancing knowledge through technology and AI. Discovery is far from over.
