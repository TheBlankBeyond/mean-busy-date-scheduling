import TBB.CheckerCore

namespace TBB

/-- Queyranne's published three-job example with exact rational endpoint witnesses. -/
def benchmark : RawCertificate :=
  let phase (a b : ℚ) (assigned : List (Nat × Nat)) (left right : ℚ) : RawPhase :=
    ⟨a, b, assigned, left, right⟩
  { n := 3, m := 2, work := [1, 1, 1], alpha := [11, 10, 9],
    multiplier := [31/2, 29/2, 279/20], horizon := 6,
    individualMoments := [1/2, 281/400, 21/20], objective := 879/40,
    schedule :=
      [phase 0 (11/20) [(0, 0), (1, 1)] (29/2) 9,
       phase (11/20) 1 [(0, 0), (1, 2)] 9 (9/2),
       phase 1 (29/20) [(0, 1), (1, 2)] (9/2) 0,
       phase (29/20) (31/20) [(1, 2)] 0 0,
       phase (31/20) 6 [] 0 0] }

end TBB
