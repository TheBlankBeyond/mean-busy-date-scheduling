import TBB.BenchmarkData

namespace TBB

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The exact published fixture passes by kernel reduction. -/
theorem benchmark_accepts : check benchmark = true := by decide +kernel

end TBB
