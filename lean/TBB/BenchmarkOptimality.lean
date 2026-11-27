import TBB.Benchmark
import TBB.Checker

namespace TBB

/-- The accepted benchmark represents a feasible globally optimal schedule with
the stated exact objective; the comparison class in `Certificate.Sound` is measurable. -/
theorem benchmark_optimal :
    ∃ c : Certificate benchmark.n benchmark.m,
      benchmark.decode = some c ∧ c.Sound ∧
      c.schedule.toMeasurable.cost c.alpha = ENNReal.ofReal ((879 / 40 : ℚ) : ℝ) := by
  obtain ⟨c, hd, hs⟩ := check_sound benchmark_accepts
  refine ⟨c, hd, hs, ?_⟩
  exact hs.objective.trans
    (congrArg (fun cost : ℚ => ENNReal.ofReal (cost : ℝ)) (RawCertificate.decode_objective hd))

end TBB
