import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Pairwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace TBB

/-- On [start, stop), the listed pairs specify the active machine and job. -/
structure Phase (n m : ℕ) where
  start : ℚ
  stop : ℚ
  assigned : List (Fin m × Fin n)
  deriving DecidableEq, Repr

namespace Phase

def active {n m : ℕ} (I : Phase n m) (j : Fin n) : Prop :=
  j ∈ I.assigned.map Prod.snd

instance {n m : ℕ} (I : Phase n m) (j : Fin n) : Decidable (I.active j) :=
  inferInstanceAs (Decidable (j ∈ I.assigned.map Prod.snd))

def work {n m : ℕ} (I : Phase n m) (j : Fin n) : ℚ :=
  if I.active j then I.stop - I.start else 0

def moment {n m : ℕ} (I : Phase n m) (j : Fin n) : ℚ :=
  if I.active j then (I.stop ^ 2 - I.start ^ 2) / 2 else 0

end Phase

/-- A list of simultaneous activity phases. Outside these intervals the machines idle. -/
abbrev Schedule (n m : ℕ) := List (Phase n m)

namespace Schedule

structure ValidAt {n m : ℕ} (S : Schedule n m) (H : ℚ) : Prop where
  ordered : S.Pairwise (fun I J => I.stop ≤ J.start)
  bounds : ∀ I ∈ S, 0 ≤ I.start ∧ I.start < I.stop ∧ I.stop ≤ H
  machines : ∀ I ∈ S, (I.assigned.map Prod.fst).Nodup
  jobs : ∀ I ∈ S, (I.assigned.map Prod.snd).Nodup

def work {n m : ℕ} (S : Schedule n m) (j : Fin n) : ℚ :=
  (S.map (fun I => I.work j)).sum

def moment {n m : ℕ} (S : Schedule n m) (j : Fin n) : ℚ :=
  (S.map (fun I => I.moment j)).sum

open scoped BigOperators in
def cost {n m : ℕ} (S : Schedule n m) (α : Fin n → ℚ) : ℚ :=
  ∑ j, α j * S.moment j

end Schedule

end TBB
