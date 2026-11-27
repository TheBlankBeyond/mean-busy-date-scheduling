# Formal mathematical supplement

The Blank Beyond · manuscript version 27 November 2026

Install Elan with the pinned Lean 4.36.0 toolchain and run these commands from the Lean project directory.

~~~sh
lean --version
lake build TBB
lake env lean TBB/AxiomAudit.lean
lake env lean TBB/BenchmarkOptimality.lean
~~~

The Lake manifest pins Mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and pins its public dependencies. A first build may fetch public sources and upstream build assets. Use a disposable build account or sandbox without personal data or credential access. Record compiler and dependency revisions. Authenticate public artifacts before using them.

To recheck the 52 historical audit roots and their dependency closure using the independent kernels bundled with Lean 4.36.0, export the proof terms and use Lake's sandboxed validator in a compatible Linux environment.

~~~bash
mapfile -t roots < <(awk '/^#print axioms / {print $3}' TBB/AxiomAudit.lean)
lake env leanexport TBB -- "${roots[@]}" > principal.ndjson
lake check --from-export principal.ndjson --paranoid
~~~

The original verification used Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Lean 4.19.0 falls within the documented affected ranges for CVE-2026-72711 and CVE-2026-72844. The Lean 4.36.0 recheck rebuilt the project modules using public Mathlib dependency cache artifacts. Independent proof validation checked the exported dependency closure of the 52 audit roots, including the dependency declarations themselves. The axiom report matched the original.

The recorded `lake check --paranoid` run checked the export with Lean's default and paranoid kernels and the release-bundled independent implementations [nanoda](https://github.com/ammkrn/nanoda_lib) (`nanoda_bin` 0.4.17), Lean4Lean (`lean4lean`), `con-leche` and `con-ron`. Lean4Lean, con-leche and con-ron are identified by the bundled binaries from the pinned Lean release. A direct nanoda run also succeeded with a hard failure policy for axioms outside `propext`, `Classical.choice` and `Quot.sound`. Comparator checked eight principal theorem statements and four named definitions against a separately specified challenge in the patched environment.

The managed environment denied Lake's nested sandbox setup. The recorded Lake validation used the expert override on local exports within the outer managed, network-restricted sandbox. The commands above retain Lake's standard isolation. [Lean release notes on kernel fixes](https://lean-lang.org/doc/reference/latest/releases/v4.33.0/) · [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

`TBB.check` in `TBB/CheckerCore.lean` evaluates a typed exact rational certificate. `TBB.check_sound` in `TBB/Checker.lean` proves global optimality over unrestricted measurable schedules for the instance encoded by an accepted certificate. `TBB.benchmark_optimal` proves the value `879/40` using kernel-checked benchmark acceptance. This scope covers the schedule realization and certificate theorems. The proof of polynomial bit complexity remains conventional mathematics.

In the complete publication bundle, the [verification instructions](../verification/README.md) link to the typed benchmark and model-to-theorem map.
