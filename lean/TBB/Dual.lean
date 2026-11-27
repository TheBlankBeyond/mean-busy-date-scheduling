import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace TBB

open scoped BigOperators

variable {n : ℕ}

/-- Pointwise rate vectors for unit speed, at most one unit per job, and machine capacity. -/
def RateFeasible (m : ℕ) (u : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ u j ∧ u j ≤ 1) ∧ (∑ j, u j) ≤ (m : ℝ)

/-- Affine multiplier scores in the raw-moment convention. -/
def score (α multiplier : Fin n → ℚ) (t : ℝ) (j : Fin n) : ℝ :=
  (multiplier j : ℝ) - t * (α j : ℝ)

def scoreValue (c u : Fin n → ℝ) : ℝ := ∑ j, c j * u j

/-- Support of the pointwise rate polytope. -/
noncomputable def supportFunction (m : ℕ) (c : Fin n → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ u, RateFeasible m u ∧ x = scoreValue c u}

/-- A nonnegative exact scalar threshold supplies an upper bound for all pointwise rates. -/
noncomputable def thresholdBound (m : ℕ) (c : Fin n → ℝ) (μ : ℝ) : ℝ :=
  (m : ℝ) * μ + ∑ j, max (c j - μ) 0

theorem rateFeasible_of_binary_capacity {m : ℕ} {u : Fin n → ℝ}
    (hbin : ∀ j, u j = 0 ∨ u j = 1) (hcap : (∑ j, u j) ≤ (m : ℝ)) :
    RateFeasible m u := by
  refine ⟨fun j => ?_, hcap⟩
  rcases hbin j with h | h <;> rw [h] <;> norm_num

theorem threshold_upper {m : ℕ} {c u : Fin n → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hu : RateFeasible m u) :
    scoreValue c u ≤ thresholdBound m c μ := by
  have hterm : ∀ j, (c j - μ) * u j ≤ max (c j - μ) 0 := by
    intro j
    by_cases h : 0 ≤ c j - μ
    · rw [max_eq_left h]
      exact mul_le_of_le_one_right h (hu.1 j).2
    · rw [max_eq_right (le_of_not_ge h)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (hu.1 j).1
  calc
    scoreValue c u = μ * (∑ j, u j) + ∑ j, (c j - μ) * u j := by
      unfold scoreValue
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ thresholdBound m c μ := by
      unfold thresholdBound
      exact add_le_add
        (by simpa only [mul_comm (m : ℝ) μ] using mul_le_mul_of_nonneg_left hu.2 hμ)
        (Finset.sum_le_sum fun j _ => hterm j)

theorem score_le_support {m : ℕ} {c u : Fin n → ℝ} (hu : RateFeasible m u) :
    scoreValue c u ≤ supportFunction m c := by
  unfold supportFunction
  apply le_csSup
  · use thresholdBound m c 0
    rintro x ⟨v, hv, rfl⟩
    exact threshold_upper le_rfl hv
  · exact ⟨u, hu, rfl⟩

theorem support_eq_of_max {m : ℕ} {c v : Fin n → ℝ} (hv : RateFeasible m v)
    (hmax : ∀ u, RateFeasible m u → scoreValue c u ≤ scoreValue c v) :
    supportFunction m c = scoreValue c v := by
  refine le_antisymm ?_ (score_le_support hv)
  unfold supportFunction
  apply csSup_le
  · exact ⟨scoreValue c v, v, hv, rfl⟩
  · rintro x ⟨u, hu, rfl⟩
    exact hmax u hu

theorem support_eq_of_threshold {m : ℕ} {c v : Fin n → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hv : RateFeasible m v) (heq : scoreValue c v = thresholdBound m c μ) :
    supportFunction m c = scoreValue c v := by
  apply support_eq_of_max hv
  intro u hu
  rw [heq]
  exact threshold_upper hμ hu

/-- Affine comparison at the two endpoints, including coincident endpoints and score ties. -/
theorem score_le_between {α multiplier : Fin n → ℚ} {u v : Fin n → ℝ} {a b t : ℝ}
    (hat : a ≤ t) (htb : t ≤ b)
    (ha : scoreValue (score α multiplier a) u ≤ scoreValue (score α multiplier a) v)
    (hb : scoreValue (score α multiplier b) u ≤ scoreValue (score α multiplier b) v) :
    scoreValue (score α multiplier t) u ≤ scoreValue (score α multiplier t) v := by
  have hlin (z : Fin n → ℝ) :
      (b - a) * scoreValue (score α multiplier t) z =
        (b - t) * scoreValue (score α multiplier a) z + (t - a) * scoreValue (score α multiplier b) z := by
    unfold scoreValue
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, score]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rcases (le_trans hat htb).lt_or_eq with hab | hab
  · apply (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp
    rw [hlin u, hlin v]
    exact add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr htb))
      (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hat))
  · have ht : t = a := by linarith
    simpa only [ht] using ha

theorem threshold_optimal_between {m : ℕ} {α multiplier : Fin n → ℚ} {u v : Fin n → ℝ}
    {a b t μa μb : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hu : RateFeasible m u) (hμa : 0 ≤ μa) (hμb : 0 ≤ μb)
    (ha : scoreValue (score α multiplier a) v = thresholdBound m (score α multiplier a) μa)
    (hb : scoreValue (score α multiplier b) v = thresholdBound m (score α multiplier b) μb) :
    scoreValue (score α multiplier t) u ≤ scoreValue (score α multiplier t) v := by
  apply score_le_between hat htb
  · rw [ha]
    exact threshold_upper hμa hu
  · rw [hb]
    exact threshold_upper hμb hu

/-- An assignment certified at both endpoints attains actual support throughout. -/
theorem support_eq_between {m : ℕ} {α multiplier : Fin n → ℚ} {v : Fin n → ℝ}
    {a b t μa μb : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hv : RateFeasible m v) (hμa : 0 ≤ μa) (hμb : 0 ≤ μb)
    (ha : scoreValue (score α multiplier a) v = thresholdBound m (score α multiplier a) μa)
    (hb : scoreValue (score α multiplier b) v = thresholdBound m (score α multiplier b) μb) :
    supportFunction m (score α multiplier t) = scoreValue (score α multiplier t) v :=
  support_eq_of_max hv fun _ hu => threshold_optimal_between hat htb hu hμa hμb ha hb

theorem score_nonpositive_of_tail {α multiplier : Fin n → ℚ} {H t : ℝ} (ht : H ≤ t)
    (hα : ∀ j, 0 ≤ (α j : ℝ)) (htail : ∀ j, score α multiplier H j ≤ 0) (j : Fin n) :
    score α multiplier t j ≤ 0 := by
  apply le_trans _ (htail j)
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right ht (hα j)) (multiplier j : ℝ)

theorem tail_optimal {m : ℕ} {α multiplier : Fin n → ℚ} {u : Fin n → ℝ} {H t : ℝ}
    (ht : H ≤ t) (hα : ∀ j, 0 ≤ (α j : ℝ)) (htail : ∀ j, score α multiplier H j ≤ 0)
    (hu : RateFeasible m u) :
    scoreValue (score α multiplier t) u ≤ scoreValue (score α multiplier t) (fun _ => 0) := by
  simp only [scoreValue, mul_zero, Finset.sum_const_zero]
  exact Finset.sum_nonpos fun j _ =>
    mul_nonpos_of_nonpos_of_nonneg (score_nonpositive_of_tail ht hα htail j) (hu.1 j).1

theorem support_eq_zero_on_tail {m : ℕ} {α multiplier : Fin n → ℚ} {H t : ℝ}
    (ht : H ≤ t) (hα : ∀ j, 0 ≤ (α j : ℝ)) (htail : ∀ j, score α multiplier H j ≤ 0) :
    supportFunction m (score α multiplier t) = 0 := by
  have hv : RateFeasible (n := n) m (fun _ => 0) := by
    simp [RateFeasible]
  simpa [scoreValue] using
    (support_eq_of_max hv fun _ hu => tail_optimal ht hα htail hu)

end TBB
