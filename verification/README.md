# Verify the exact example

The Blank Beyond · manuscript revision 2 · 27 November 2026

The essential certificate fixture is the typed Lean term TBB.benchmark in [BenchmarkData.lean](../lean/TBB/BenchmarkData.lean). It contains three unit-work jobs, two machines, coefficients (11, 10, 9), the optimal schedule, rational multipliers and endpoint thresholds. The paper gives all fields and the exact costs.

From the lean directory after building:

~~~sh
lake env lean TBB/Benchmark.lean
lake env lean TBB/BenchmarkOptimality.lean
lake env lean TBB/AxiomAudit.lean
~~~

TBB.benchmark_accepts is checked by Lean kernel reduction. TBB.benchmark_optimal certifies the value 879/40 against arbitrary feasible measurable schedules. A reader supplying another typed certificate should verify the instance fields and can evaluate TBB.check on it. Executable evaluation is empirical evidence for the input evaluated. TBB.check_sound is the general kernel theorem connecting acceptance to the represented schedule's global optimality.

The archived bulk tests and independently generated cases reported in the manuscript were checked privately. The public supplement supports the kernel benchmark, axiom audit and evaluations of reader-supplied typed certificates.

## Formal verification map

| Mathematical content | Lean source and declarations |
|---|---|
| Measurable problem and objective conversion | [Measurable.lean](../lean/TBB/Measurable.lean), TBB.MeasurableSchedule.Feasible, normalizedCost_eq_cost, cost_eq_normalizedCost |
| Equivalence with measurable labeled machines | [Machines.lean](../lean/TBB/Machines.lean), TBB.MeasurableSchedule.labeled_feasible and labeled_same_cost |
| Reflected records, feasibility, work, first moments and count | [Realization.lean](../lean/TBB/Realization.lean), TBB.reflected_realization_on_line, TBB.reflected_realization, TBB.realizePhase_machine_min, TBB.realize_restrict_phase_on_line |
| Analytic interpretation of records | [OperationBridge.lean](../lean/TBB/OperationBridge.lean), TBB.realize_phase_measurable, TBB.realize_measurable_totals |
| Tail, endpoint support inequalities and exact integral | [Checker.lean](../lean/TBB/Checker.lean), TBB.Certificate.Passes.score_compare and support_integral_eq |
| Measurable dual bound and exact optimality | [Optimality.lean](../lean/TBB/Optimality.lean), TBB.dual_lower_bound_additive and TBB.optimal_of_exact_dual |
| Exact executable checker and unrestricted soundness | [CheckerCore.lean](../lean/TBB/CheckerCore.lean), [Checker.lean](../lean/TBB/Checker.lean), TBB.check, TBB.check_sound and TBB.Certificate.Sound.optimal_aeActivity |
| Exact original example | [Benchmark.lean](../lean/TBB/Benchmark.lean) and [BenchmarkOptimality.lean](../lean/TBB/BenchmarkOptimality.lean), TBB.benchmark_accepts and TBB.benchmark_optimal |

The provided audit covers 52 declarations. The standard foundational axioms in its output are propext, Classical.choice and Quot.sound. Theorem Q, including the GLS routine, recovery chain and Turing complexity proof, is conventional and is given in the paper.
