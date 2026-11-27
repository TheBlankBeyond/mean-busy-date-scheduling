import TBB.Finite
import TBB.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.BigOperators

open Filter MeasureTheory
open scoped ENNReal BigOperators

namespace TBB

namespace Phase

variable {n m : ℕ}

/-- The half-open real processing interval represented by a rational phase. -/
def timeSet (I : Phase n m) : Set ℝ := Set.Ico (I.start : ℝ) (I.stop : ℝ)

theorem measurableSet_timeSet (I : Phase n m) : MeasurableSet I.timeSet :=
  measurableSet_Ico

/-- The activity of a job within a single phase, zero outside the phase. -/
noncomputable def realActivity (I : Phase n m) (j : Fin n) : ℝ → ℝ :=
  I.timeSet.indicator (fun _ => if I.active j then 1 else 0)

theorem realActivity_measurable (I : Phase n m) (j : Fin n) :
    Measurable (I.realActivity j) :=
  measurable_const.indicator I.measurableSet_timeSet

theorem realActivity_at (I : Phase n m) (j : Fin n) {t : ℝ} (ht : t ∈ I.timeSet) :
    I.realActivity j t = if I.active j then 1 else 0 := by
  exact Set.indicator_of_mem ht _

theorem realActivity_off (I : Phase n m) (j : Fin n) {t : ℝ} (ht : t ∉ I.timeSet) :
    I.realActivity j t = 0 := by
  simp [realActivity, ht]

theorem realActivity_nonneg (I : Phase n m) (j : Fin n) (t : ℝ) : 0 ≤ I.realActivity j t := by
  by_cases ht : t ∈ I.timeSet
  · rw [I.realActivity_at j ht]
    split
    · exact zero_le_one
    · exact le_rfl
  · rw [I.realActivity_off j ht]

theorem activeCount_le (I : Phase n m) (hm : (I.assigned.map Prod.fst).Nodup)
    (hj : (I.assigned.map Prod.snd).Nodup) :
    (∑ j, if I.active j then (1 : ℝ) else 0) ≤ (m : ℝ) := by
  classical
  have ht : (Finset.univ.filter I.active) = (I.assigned.map Prod.snd).toFinset := by
    ext j
    simp [active]
  have hn : I.assigned.length ≤ m := by
    simpa using hm.length_le_card
  rw [Finset.sum_boole, ht, List.toFinset_card_of_nodup hj, List.length_map]
  exact_mod_cast hn

theorem work_nonneg (I : Phase n m) (j : Fin n) (hab : I.start ≤ I.stop) :
    0 ≤ I.work j := by
  unfold work
  split
  · exact sub_nonneg.mpr hab
  · exact le_rfl

theorem moment_nonneg (I : Phase n m) (j : Fin n)
    (ha : 0 ≤ I.start) (hab : I.start ≤ I.stop) : 0 ≤ I.moment j := by
  unfold moment
  split
  · exact div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha hab _)) zero_le_two
  · exact le_rfl

private theorem timeMeasure_restrict (I : Phase n m) (ha : 0 ≤ I.start) :
    timeMeasure.restrict I.timeSet = volume.restrict I.timeSet := by
  unfold timeMeasure
  rw [Measure.restrict_restrict I.measurableSet_timeSet]
  congr 1
  apply Set.inter_eq_left.mpr
  intro t ht
  have h0 : (0 : ℝ) ≤ (I.start : ℝ) := by exact_mod_cast ha
  exact h0.trans ht.1

theorem lintegral_realActivity (I : Phase n m) (j : Fin n) (ha : 0 ≤ I.start) :
    (∫⁻ t, ENNReal.ofReal (I.realActivity j t) ∂timeMeasure) =
      ENNReal.ofReal (I.work j : ℝ) := by
  by_cases hj : I.active j
  · have he : (fun t => ENNReal.ofReal (I.realActivity j t)) =
        I.timeSet.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext t
      by_cases ht : t ∈ I.timeSet
      · simp [I.realActivity_at j ht, ht, hj]
      · simp [I.realActivity_off j ht, ht]
    rw [he, lintegral_indicator I.measurableSet_timeSet, I.timeMeasure_restrict ha, lintegral_const]
    simp [Measure.restrict_apply_univ, timeSet, work, hj, Real.volume_Ico]
  · have he : ∀ t, I.realActivity j t = 0 := by
      intro t
      simp [realActivity, hj]
    simp [he, work, hj]

private theorem intervalIntegral_identity (a b : ℝ) :
    (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by
  have hr := intervalIntegral.integral_comp_sub_left (a := a) (b := b) (fun t : ℝ => t) (a + b)
  rw [show a + b - b = a by ring, show a + b - a = b by ring] at hr
  change (∫ x in a..b, (a + b) - x) = (∫ x in a..b, x) at hr
  have hconst : IntervalIntegrable (fun _ : ℝ => a + b) volume a b := intervalIntegrable_const
  have hid : IntervalIntegrable (fun x : ℝ => x) volume a b := continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const, smul_eq_mul] at hr
  nlinarith

theorem lintegral_mul_realActivity (I : Phase n m) (j : Fin n) (ha : 0 ≤ I.start)
    (hab : I.start ≤ I.stop) :
    (∫⁻ t, ENNReal.ofReal (t * I.realActivity j t) ∂timeMeasure) =
      ENNReal.ofReal (I.moment j : ℝ) := by
  by_cases hj : I.active j
  · have he : (fun t => ENNReal.ofReal (t * I.realActivity j t)) =
        I.timeSet.indicator ENNReal.ofReal := by
      funext t
      by_cases ht : t ∈ I.timeSet
      · simp [I.realActivity_at j ht, ht, hj]
      · simp [I.realActivity_off j ht, ht]
    have h0 : (0 : ℝ) ≤ (I.start : ℝ) := by exact_mod_cast ha
    have hr : (I.start : ℝ) ≤ (I.stop : ℝ) := by exact_mod_cast hab
    have hpos : ∀ᵐ (t : ℝ) ∂volume.restrict I.timeSet, 0 ≤ t :=
      (ae_restrict_mem I.measurableSet_timeSet).mono (fun _ ht => h0.trans ht.1)
    have hi : IntervalIntegrable (fun t : ℝ => t) volume (I.start : ℝ) (I.stop : ℝ) :=
      continuous_id.intervalIntegrable _ _
    have hi' : Integrable (fun t : ℝ => t) (volume.restrict I.timeSet) :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le hr).mp hi
    rw [he, lintegral_indicator I.measurableSet_timeSet, I.timeMeasure_restrict ha,
      ← ofReal_integral_eq_lintegral_ofReal hi' hpos]
    unfold timeSet
    rw [Measure.restrict_congr_set (μ := volume) Ico_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le hr, intervalIntegral_identity]
    simp [moment, hj]
  · have he : ∀ t, I.realActivity j t = 0 := by
      intro t
      simp [realActivity, hj]
    simp [he, moment, hj]

end Phase

namespace Schedule

variable {n m : ℕ}

/-- Sum the per-phase activities, with the idle value zero for an empty list. -/
noncomputable def realActivity (S : Schedule n m) (j : Fin n) (t : ℝ) : ℝ :=
  (S.map fun I => I.realActivity j t).sum

theorem realActivity_measurable (S : Schedule n m) (j : Fin n) :
    Measurable (realActivity S j) := by
  induction S with
  | nil => change Measurable (fun _ : ℝ => (0 : ℝ)); exact measurable_const
  | cons I S ih => exact (I.realActivity_measurable j).add ih

theorem realActivity_nonneg (S : Schedule n m) (j : Fin n) (t : ℝ) :
    0 ≤ realActivity S j t := by
  induction S with
  | nil => exact le_rfl
  | cons I S ih => exact add_nonneg (I.realActivity_nonneg j t) ih

/-- Interpret a finite interval schedule as a measurable activity function off the grid as well. -/
noncomputable def toMeasurable (S : Schedule n m) : MeasurableSchedule n :=
  ⟨realActivity S, realActivity_measurable S⟩

theorem activity_zero_of_no_phase (S : Schedule n m) {t : ℝ}
    (ht : ∀ I ∈ S, t ∉ I.timeSet) (j : Fin n) :
    (toMeasurable S).activity j t = 0 := by
  induction S with
  | nil => rfl
  | cons I S ih =>
    change I.realActivity j t + (toMeasurable S).activity j t = 0
    rw [I.realActivity_off j (ht I (by simp)), ih (fun J hJ => ht J (by simp [hJ])), add_zero]

private theorem activity_eq_phase_of_ordered {S : Schedule n m}
    (hS : S.Pairwise (fun I J => I.stop ≤ J.start))
    {I : Phase n m} (hI : I ∈ S) {t : ℝ} (ht : t ∈ I.timeSet) (j : Fin n) :
    (toMeasurable S).activity j t = if I.active j then 1 else 0 := by
  induction S with
  | nil => simp at hI
  | cons A S ih =>
    have hn := List.pairwise_cons.mp hS
    change A.realActivity j t + (toMeasurable S).activity j t = _
    rcases List.mem_cons.mp hI with heq | hi
    · subst I
      rw [A.realActivity_at j ht, activity_zero_of_no_phase S ?_ j, add_zero]
      intro J hJ htJ
      have hsep : (A.stop : ℝ) ≤ (J.start : ℝ) := by exact_mod_cast hn.1 J hJ
      exact (not_le_of_gt ht.2) (hsep.trans htJ.1)
    · have hsep : (A.stop : ℝ) ≤ (I.start : ℝ) := by exact_mod_cast hn.1 I hi
      have htA : t ∉ A.timeSet := fun hh => (not_le_of_gt hh.2) (hsep.trans ht.1)
      rw [A.realActivity_off j htA, zero_add, ih hn.2 hi]

theorem activity_eq_phase {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H)
    {I : Phase n m} (hI : I ∈ S) {t : ℝ} (ht : t ∈ I.timeSet) (j : Fin n) :
    (toMeasurable S).activity j t = if I.active j then 1 else 0 :=
  activity_eq_phase_of_ordered hS.ordered hI ht j

theorem activity_binary {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H) (t : ℝ) (j : Fin n) :
    (toMeasurable S).activity j t = 0 ∨ (toMeasurable S).activity j t = 1 := by
  classical
  by_cases ht : ∃ I ∈ S, t ∈ I.timeSet
  · obtain ⟨I, hI, htI⟩ := ht
    rw [activity_eq_phase hS hI htI j]
    split <;> simp
  · exact Or.inl (activity_zero_of_no_phase S (fun I hI h => ht ⟨I, hI, h⟩) j)

theorem activity_capacity {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H) (t : ℝ) :
    (∑ j, (toMeasurable S).activity j t) ≤ (m : ℝ) := by
  classical
  by_cases ht : ∃ I ∈ S, t ∈ I.timeSet
  · obtain ⟨I, hI, htI⟩ := ht
    simp_rw [activity_eq_phase hS hI htI]
    exact I.activeCount_le (hS.machines I hI) (hS.jobs I hI)
  · simp [activity_zero_of_no_phase S (fun I hI h => ht ⟨I, hI, h⟩)]

private theorem work_nonneg_aux (S : Schedule n m) (j : Fin n)
    (hb : ∀ I ∈ S, I.start ≤ I.stop) : 0 ≤ work S j := by
  induction S with
  | nil => exact le_rfl
  | cons I S ih =>
    exact add_nonneg (I.work_nonneg j (hb I (by simp)))
      (ih (fun J hJ => hb J (by simp [hJ])))

private theorem moment_nonneg_aux (S : Schedule n m) (j : Fin n)
    (hb : ∀ I ∈ S, 0 ≤ I.start ∧ I.start ≤ I.stop) : 0 ≤ moment S j := by
  induction S with
  | nil => exact le_rfl
  | cons I S ih =>
    have hI := hb I (by simp)
    exact add_nonneg (I.moment_nonneg j hI.1 hI.2) (ih (fun J hJ => hb J (by simp [hJ])))

theorem moment_nonneg {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H) (j : Fin n) :
    0 ≤ moment S j :=
  moment_nonneg_aux S j (fun I hI => ⟨(hS.bounds I hI).1, (hS.bounds I hI).2.1.le⟩)

theorem toMeasurable_work_aux (S : Schedule n m) (j : Fin n)
    (hb : ∀ I ∈ S, 0 ≤ I.start ∧ I.start ≤ I.stop) :
    (toMeasurable S).work j = ENNReal.ofReal (work S j : ℝ) := by
  induction S with
  | nil =>
    simp [MeasurableSchedule.work, toMeasurable, realActivity, work]
  | cons I S ih =>
    have hI := hb I (by simp)
    have htail : ∀ J ∈ S, 0 ≤ J.start ∧ J.start ≤ J.stop :=
      fun J hJ => hb J (by simp [hJ])
    have h1 := I.lintegral_realActivity j hI.1
    have h2 := ih htail
    have he : (fun t => ENNReal.ofReal ((toMeasurable (I :: S)).activity j t)) =
        fun t => ENNReal.ofReal (I.realActivity j t) +
          ENNReal.ofReal ((toMeasurable S).activity j t) := by
      funext t
      exact ENNReal.ofReal_add (I.realActivity_nonneg j t) (realActivity_nonneg S j t)
    unfold MeasurableSchedule.work at h2 ⊢
    rw [he, lintegral_add_left ((I.realActivity_measurable j).ennreal_ofReal), h1, h2]
    simp only [work, List.map_cons, List.sum_cons, Rat.cast_add]
    have hnI : (0 : ℝ) ≤ (I.work j : ℝ) := Rat.cast_nonneg.mpr (I.work_nonneg j hI.2)
    have hnS : (0 : ℝ) ≤ (work S j : ℝ) :=
      Rat.cast_nonneg.mpr (work_nonneg_aux S j (fun J hJ => (htail J hJ).2))
    exact (ENNReal.ofReal_add hnI hnS).symm

/-- The exact per-job rational length agrees with the workload Lebesgue integral. -/
theorem toMeasurable_work {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H) (j : Fin n) :
    (toMeasurable S).work j = ENNReal.ofReal (work S j : ℝ) :=
  toMeasurable_work_aux S j (fun I hI => ⟨(hS.bounds I hI).1, (hS.bounds I hI).2.1.le⟩)

theorem toMeasurable_moment_aux (S : Schedule n m) (j : Fin n)
    (hb : ∀ I ∈ S, 0 ≤ I.start ∧ I.start ≤ I.stop) :
    (toMeasurable S).moment j = ENNReal.ofReal (moment S j : ℝ) := by
  induction S with
  | nil =>
    simp [MeasurableSchedule.moment, toMeasurable, realActivity, moment]
  | cons I S ih =>
    have hI := hb I (by simp)
    have htail : ∀ J ∈ S, 0 ≤ J.start ∧ J.start ≤ J.stop :=
      fun J hJ => hb J (by simp [hJ])
    have h1 := I.lintegral_mul_realActivity j hI.1 hI.2
    have h2 := ih htail
    have he :
        (fun t => ENNReal.ofReal (t * (toMeasurable (I :: S)).activity j t))
          =ᵐ[timeMeasure] fun t => ENNReal.ofReal (t * I.realActivity j t) +
            ENNReal.ofReal (t * (toMeasurable S).activity j t) := by
      apply ae_time_nonneg.mono
      intro t ht
      change ENNReal.ofReal (t * (I.realActivity j t + realActivity S j t)) = _
      rw [mul_add]
      exact ENNReal.ofReal_add (mul_nonneg ht (I.realActivity_nonneg j t))
        (mul_nonneg ht (realActivity_nonneg S j t))
    have hm : Measurable (fun t => ENNReal.ofReal (t * I.realActivity j t)) :=
      (measurable_id.mul (I.realActivity_measurable j)).ennreal_ofReal
    unfold MeasurableSchedule.moment at h2 ⊢
    rw [lintegral_congr_ae he, lintegral_add_left hm, h1, h2]
    simp only [moment, List.map_cons, List.sum_cons, Rat.cast_add]
    have hnI : (0 : ℝ) ≤ (I.moment j : ℝ) :=
      Rat.cast_nonneg.mpr (I.moment_nonneg j hI.1 hI.2)
    have hnS : (0 : ℝ) ≤ (moment S j : ℝ) := Rat.cast_nonneg.mpr (moment_nonneg_aux S j htail)
    exact (ENNReal.ofReal_add hnI hnS).symm

/-- The exact individual rational first moment agrees with the Lebesgue moment. -/
theorem toMeasurable_moment {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H) (j : Fin n) :
    (toMeasurable S).moment j = ENNReal.ofReal (moment S j : ℝ) :=
  toMeasurable_moment_aux S j (fun I hI => ⟨(hS.bounds I hI).1, (hS.bounds I hI).2.1.le⟩)

/-- Feasible finite rational witnesses belong to the unrestricted comparator class. -/
theorem toMeasurable_feasible {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H)
    {p : Fin n → ℚ} (hw : ∀ j, work S j = p j) : (toMeasurable S).Feasible m p where
  binary := Filter.Eventually.of_forall (fun t j => activity_binary hS t j)
  capacity := Filter.Eventually.of_forall (activity_capacity hS)
  workload := fun j => by rw [toMeasurable_work hS j, hw j]

/-- Exact rational weighted cost agrees with the objective on the unbounded domain. -/
theorem toMeasurable_cost {S : Schedule n m} {H : ℚ} (hS : S.ValidAt H)
    {α : Fin n → ℚ} (hα : ∀ j, 0 ≤ α j) :
    (toMeasurable S).cost α = ENNReal.ofReal (cost S α : ℝ) := by
  have hαr (j : Fin n) : (0 : ℝ) ≤ (α j : ℝ) := by exact_mod_cast hα j
  have hsr (j : Fin n) : (0 : ℝ) ≤ (moment S j : ℝ) :=
    Rat.cast_nonneg.mpr (moment_nonneg hS j)
  unfold MeasurableSchedule.cost cost
  simp only [Rat.cast_sum, Rat.cast_mul]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hαr j) (hsr j))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toMeasurable_moment hS j, ENNReal.ofReal_mul (hαr j)]

end Schedule
end TBB
