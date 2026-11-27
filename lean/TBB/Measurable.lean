import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.Rat.Cast.Order

open Filter MeasureTheory
open scoped ENNReal BigOperators

namespace TBB

/-- Lebesgue measure on the entire nonnegative time domain. -/
noncomputable def timeMeasure : Measure ℝ := volume.restrict (Set.Ici 0)

theorem ae_time_nonneg : ∀ᵐ t ∂timeMeasure, (0 : ℝ) ≤ t := by
  exact ae_restrict_mem measurableSet_Ici

/-- A schedule in job-activity coordinates. Binary activity means a job uses at most
one machine. Capacity limits the number of simultaneously active jobs. Measurable
activity permits arbitrary preemption and migration. -/
structure MeasurableSchedule (n : ℕ) where
  activity : Fin n → ℝ → ℝ
  measurable_activity : ∀ j, Measurable (activity j)

namespace MeasurableSchedule

variable {n : ℕ}

/-- The nonnegative integral of a job's activity on the time domain. -/
noncomputable def work (S : MeasurableSchedule n) (j : Fin n) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (S.activity j t) ∂timeMeasure

/-- The first moment, with infinite moments represented by `⊤`. -/
noncomputable def moment (S : MeasurableSchedule n) (j : Fin n) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (t * S.activity j t) ∂timeMeasure

/-- Queyranne's weighted raw first-moment objective. -/
noncomputable def cost (S : MeasurableSchedule n) (α : Fin n → ℚ) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (α j : ℝ) * S.moment j

/-- Feasibility in the unrestricted measurable scheduling model. -/
structure Feasible (S : MeasurableSchedule n) (m : ℕ) (p : Fin n → ℚ) : Prop where
  binary : ∀ᵐ t ∂timeMeasure, ∀ j, S.activity j t = 0 ∨ S.activity j t = 1
  capacity : ∀ᵐ t ∂timeMeasure, ∑ j, S.activity j t ≤ (m : ℝ)
  workload : ∀ j, S.work j = ENNReal.ofReal (p j : ℝ)

/-- A normalized mean busy date uses the workload as a scale factor. -/
noncomputable def meanBusyDate (S : MeasurableSchedule n) (p : Fin n → ℚ) (j : Fin n) : ℝ≥0∞ :=
  S.moment j / ENNReal.ofReal (p j : ℝ)

/-- The alternative objective that weights normalized mean busy dates. -/
noncomputable def normalizedCost (S : MeasurableSchedule n) (p w : Fin n → ℚ) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (w j : ℝ) * S.meanBusyDate p j

/-- Convert normalized weights to raw-moment coefficients, including for infinite moments. -/
theorem normalizedCost_eq_cost (S : MeasurableSchedule n) (p w : Fin n → ℚ)
    (hp : ∀ j, 0 < p j) :
    S.normalizedCost p w = S.cost (fun j => w j / p j) := by
  unfold normalizedCost cost
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpr : (0 : ℝ) < (p j : ℝ) := Rat.cast_pos.mpr (hp j)
  rw [meanBusyDate, Rat.cast_div, ENNReal.ofReal_div_of_pos hpr]
  simp only [div_eq_mul_inv]
  ac_rfl

/-- Convert raw-moment coefficients to weights on normalized mean busy dates. -/
theorem cost_eq_normalizedCost (S : MeasurableSchedule n) (p α : Fin n → ℚ)
    (hp : ∀ j, 0 < p j) :
    S.cost α = S.normalizedCost p (fun j => α j * p j) := by
  rw [normalizedCost_eq_cost S p _ hp]
  congr 1
  funext j
  exact (mul_div_cancel_right₀ (α j) (ne_of_gt (hp j))).symm

/-- Replace each almost-everywhere measurable activity by a measurable representative.
This includes Lebesgue-measurable activity supplied on the completed time domain. -/
noncomputable def ofAEActivity (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, AEMeasurable (u j) timeMeasure) : MeasurableSchedule n where
  activity j := (hu j).mk (u j)
  measurable_activity j := (hu j).measurable_mk

/-- Measurability in the completed Lebesgue domain provides the required representatives. -/
theorem completedActivity_aemeasurable (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, NullMeasurable (u j) timeMeasure) :
    ∀ j, AEMeasurable (u j) timeMeasure :=
  fun j => (hu j).aemeasurable

theorem ofAEActivity_ae (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, AEMeasurable (u j) timeMeasure) (j : Fin n) :
    (ofAEActivity u hu).activity j =ᵐ[timeMeasure] u j :=
  (hu j).ae_eq_mk.symm

theorem ofAEActivity_work (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, AEMeasurable (u j) timeMeasure) (j : Fin n) :
    (ofAEActivity u hu).work j =
      ∫⁻ t, ENNReal.ofReal (u j t) ∂timeMeasure := by
  apply lintegral_congr_ae
  filter_upwards [ofAEActivity_ae u hu j] with t ht
  rw [ht]

theorem ofAEActivity_moment (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, AEMeasurable (u j) timeMeasure) (j : Fin n) :
    (ofAEActivity u hu).moment j =
      ∫⁻ t, ENNReal.ofReal (t * u j t) ∂timeMeasure := by
  apply lintegral_congr_ae
  filter_upwards [ofAEActivity_ae u hu j] with t ht
  rw [ht]

/-- Changes on null sets preserve both feasibility and individual workloads. -/
theorem ofAEActivity_feasible {m : ℕ} {p : Fin n → ℚ}
    (u : Fin n → ℝ → ℝ) (hu : ∀ j, AEMeasurable (u j) timeMeasure)
    (hb : ∀ᵐ t ∂timeMeasure, ∀ j, u j t = 0 ∨ u j t = 1)
    (hc : ∀ᵐ t ∂timeMeasure, ∑ j, u j t ≤ (m : ℝ))
    (hw : ∀ j, (∫⁻ t, ENNReal.ofReal (u j t) ∂timeMeasure) = ENNReal.ofReal (p j : ℝ)) :
    (ofAEActivity u hu).Feasible m p := by
  have hrepl : ∀ᵐ t ∂timeMeasure, ∀ j, (ofAEActivity u hu).activity j t = u j t :=
    ae_all_iff.mpr (ofAEActivity_ae u hu)
  refine ⟨?_, ?_, fun j => (ofAEActivity_work u hu j).trans (hw j)⟩
  · filter_upwards [hrepl, hb] with t ht hb'
    intro j
    simpa only [ht j] using hb' j
  · filter_upwards [hrepl, hc] with t ht hc'
    simpa only [ht] using hc'

/-- The same change of representative preserves the weighted objective, even at infinity. -/
theorem ofAEActivity_cost (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, AEMeasurable (u j) timeMeasure) (α : Fin n → ℚ) :
    (ofAEActivity u hu).cost α =
      ∑ j, ENNReal.ofReal (α j : ℝ) * (∫⁻ t, ENNReal.ofReal (t * u j t) ∂timeMeasure) := by
  simp only [cost, ofAEActivity_moment]

end MeasurableSchedule
end TBB
