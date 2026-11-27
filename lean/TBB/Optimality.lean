import Mathlib.Data.Rat.BigOperators
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TBB.Measurable
import TBB.Dual

open Filter MeasureTheory
open scoped ENNReal BigOperators

namespace TBB

variable {n : ℕ}

private noncomputable def positiveCoeff (multiplier : Fin n → ℚ) (j : Fin n) : ℝ :=
  max (multiplier j : ℝ) 0

private noncomputable def negativeCoeff (multiplier : Fin n → ℚ) (j : Fin n) : ℝ :=
  max (-(multiplier j : ℝ)) 0

private theorem positiveCoeff_nonneg (multiplier : Fin n → ℚ) (j : Fin n) :
    0 ≤ positiveCoeff multiplier j := le_max_right _ _

private theorem negativeCoeff_nonneg (multiplier : Fin n → ℚ) (j : Fin n) :
    0 ≤ negativeCoeff multiplier j := le_max_right _ _

private theorem coeff_sub (multiplier : Fin n → ℚ) (j : Fin n) :
    positiveCoeff multiplier j - negativeCoeff multiplier j = (multiplier j : ℝ) := by
  unfold positiveCoeff negativeCoeff
  rcases le_total (0 : ℝ) (multiplier j : ℝ) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]

/-- The positive and negative parts of the signed multiplier-work pairing.
Both are finite since all required workloads are rational. -/
noncomputable def dualPositiveWork (multiplier p : Fin n → ℚ) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (positiveCoeff multiplier j) * ENNReal.ofReal (p j : ℝ)

noncomputable def dualNegativeWork (multiplier p : Fin n → ℚ) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (negativeCoeff multiplier j) * ENNReal.ofReal (p j : ℝ)

theorem dualPositiveWork_ne_top (multiplier p : Fin n → ℚ) : dualPositiveWork multiplier p ≠ ⊤ := by
  unfold dualPositiveWork
  exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top)

theorem dualNegativeWork_ne_top (multiplier p : Fin n → ℚ) : dualNegativeWork multiplier p ≠ ⊤ := by
  unfold dualNegativeWork
  exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top)

/-- The finite positive and negative work contributions reassemble the rational dot product. -/
theorem dual_work_diff_toReal (multiplier p : Fin n → ℚ) (hp : ∀ j, 0 ≤ (p j : ℝ)) :
    (dualPositiveWork multiplier p).toReal - (dualNegativeWork multiplier p).toReal =
      ((∑ j, multiplier j * p j : ℚ) : ℝ) := by
  have hconvert (β : Fin n → ℝ) (hβ : ∀ j, 0 ≤ β j) :
      (∑ j, ENNReal.ofReal (β j) * ENNReal.ofReal (p j : ℝ)).toReal =
        ∑ j, β j * (p j : ℝ) := by
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hβ j), ENNReal.toReal_ofReal (hp j)]
  unfold dualPositiveWork dualNegativeWork
  rw [hconvert _ (positiveCoeff_nonneg multiplier), hconvert _ (negativeCoeff_nonneg multiplier),
    ← Finset.sum_sub_distrib, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sub_mul, coeff_sub, Rat.cast_mul]

private noncomputable def weightedRate (β : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (t : ℝ) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (β j) * ENNReal.ofReal (f j t)

private theorem weightedRate_measurable {β : Fin n → ℝ} {f : Fin n → ℝ → ℝ}
    (hf : ∀ j, Measurable (f j)) : Measurable (weightedRate β f) := by
  unfold weightedRate
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul (hf j).ennreal_ofReal

private theorem ofReal_weighted_sum {β : Fin n → ℝ} {f : Fin n → ℝ → ℝ} {t : ℝ}
    (hβ : ∀ j, 0 ≤ β j) (hf : ∀ j, 0 ≤ f j t) :
    ENNReal.ofReal (∑ j, β j * f j t) = weightedRate β f t := by
  unfold weightedRate
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hβ j) (hf j))]
  apply Finset.sum_congr rfl
  intro j _
  exact ENNReal.ofReal_mul (hβ j)

private theorem lintegral_weightedRate {β : Fin n → ℝ} {f : Fin n → ℝ → ℝ}
    (hf : ∀ j, Measurable (f j)) :
    (∫⁻ t, weightedRate β f t ∂timeMeasure) =
      ∑ j, ENNReal.ofReal (β j) * (∫⁻ t, ENNReal.ofReal (f j t) ∂timeMeasure) := by
  unfold weightedRate
  rw [lintegral_finsetSum (f := fun j t => ENNReal.ofReal (β j) * ENNReal.ofReal (f j t))
    _ (fun j _ => measurable_const.mul (hf j).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_const_mul _ (hf j).ennreal_ofReal

private theorem lintegral_workRate {m : ℕ} {S : MeasurableSchedule n} {p : Fin n → ℚ}
    {β : Fin n → ℝ} (hS : S.Feasible m p) :
    (∫⁻ t, weightedRate β S.activity t ∂timeMeasure) =
      ∑ j, ENNReal.ofReal (β j) * ENNReal.ofReal (p j : ℝ) := by
  rw [lintegral_weightedRate S.measurable_activity]
  change (∑ j, ENNReal.ofReal (β j) * S.work j) = _
  simp only [hS.workload]

private theorem momentRate_measurable (S : MeasurableSchedule n) (j : Fin n) :
    Measurable (fun t => t * S.activity j t) :=
  measurable_id.mul (S.measurable_activity j)

private theorem lintegral_costRate (S : MeasurableSchedule n) (α : Fin n → ℚ) :
    (∫⁻ t, weightedRate (fun j => (α j : ℝ)) (fun j t => t * S.activity j t) t
      ∂timeMeasure) = S.cost α := by
  exact lintegral_weightedRate (momentRate_measurable S)

private theorem lintegral_add_three {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ t, f t + g t + h t ∂timeMeasure) =
      (∫⁻ t, f t ∂timeMeasure) + (∫⁻ t, g t ∂timeMeasure) + (∫⁻ t, h t ∂timeMeasure) := by
  change (∫⁻ t, (f + g) t + h t ∂timeMeasure) = _
  rw [lintegral_add_left (hf.add hg) h]
  change (∫⁻ t, f t + g t ∂timeMeasure) + _ = _
  rw [lintegral_add_left hf g]

theorem measurable_schedule_score (S : MeasurableSchedule n) (α multiplier : Fin n → ℚ) :
    Measurable (fun t => scoreValue (score α multiplier t) (fun j => S.activity j t)) := by
  unfold scoreValue score
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_const.sub (measurable_id.mul measurable_const)).mul (S.measurable_activity j)

private theorem score_balance (S : MeasurableSchedule n) (α multiplier : Fin n → ℚ) (t : ℝ) :
    scoreValue (score α multiplier t) (fun j => S.activity j t) =
      (∑ j, positiveCoeff multiplier j * S.activity j t) -
      (∑ j, (α j : ℝ) * (t * S.activity j t)) -
      (∑ j, negativeCoeff multiplier j * S.activity j t) := by
  unfold scoreValue score
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  calc
    ((multiplier j : ℝ) - t * (α j : ℝ)) * S.activity j t =
        ((positiveCoeff multiplier j - negativeCoeff multiplier j) - t * (α j : ℝ)) * S.activity j t := by
      rw [coeff_sub]
    _ = _ := by ring

private theorem binary_nonneg {u : Fin n → ℝ} (h : ∀ j, u j = 0 ∨ u j = 1) :
    ∀ j, 0 ≤ u j := by
  intro j
  rcases h j with hj | hj <;> simp [hj]

private theorem rate_conversion (S : MeasurableSchedule n) (α multiplier : Fin n → ℚ)
    {t r : ℝ} (ht : 0 ≤ t) (hu : ∀ j, 0 ≤ S.activity j t)
    (hα : ∀ j, 0 ≤ (α j : ℝ)) (hr : 0 ≤ r) :
    ENNReal.ofReal (∑ j, positiveCoeff multiplier j * S.activity j t) =
      weightedRate (positiveCoeff multiplier) S.activity t ∧
    ENNReal.ofReal ((∑ j, (α j : ℝ) * (t * S.activity j t)) + r +
        ∑ j, negativeCoeff multiplier j * S.activity j t) =
      weightedRate (fun j => (α j : ℝ)) (fun j t => t * S.activity j t) t +
        ENNReal.ofReal r + weightedRate (negativeCoeff multiplier) S.activity t := by
  have hm : ∀ j, 0 ≤ t * S.activity j t := fun j => mul_nonneg ht (hu j)
  have hc : 0 ≤ ∑ j, (α j : ℝ) * (t * S.activity j t) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hα j) (hm j)
  have hn : 0 ≤ ∑ j, negativeCoeff multiplier j * S.activity j t :=
    Finset.sum_nonneg fun j _ => mul_nonneg (negativeCoeff_nonneg multiplier j) (hu j)
  refine ⟨ofReal_weighted_sum (f := S.activity) (t := t) (positiveCoeff_nonneg multiplier) hu, ?_⟩
  rw [ENNReal.ofReal_add (add_nonneg hc hr) hn, ENNReal.ofReal_add hc hr,
    ofReal_weighted_sum (f := fun j t => t * S.activity j t) (t := t) hα hm,
    ofReal_weighted_sum (f := S.activity) (t := t) (negativeCoeff_nonneg multiplier) hu]

/-- Integrated dual lower bound in an additive form which also handles infinite cost.
A measurable nonnegative support majorant suffices. -/
theorem dual_lower_bound_additive {m : ℕ} {p α multiplier : Fin n → ℚ}
    {S : MeasurableSchedule n} {r : ℝ → ℝ}
    (hS : S.Feasible m p) (hα : ∀ j, 0 ≤ (α j : ℝ))
    (hr : Measurable r) (hr_nonneg : ∀ᵐ t ∂timeMeasure, 0 ≤ r t)
    (hmajor : ∀ᵐ t ∂timeMeasure,
      scoreValue (score α multiplier t) (fun j => S.activity j t) ≤ r t) :
    dualPositiveWork multiplier p ≤
      S.cost α + (∫⁻ t, ENNReal.ofReal (r t) ∂timeMeasure) + dualNegativeWork multiplier p := by
  have hp : ∀ᵐ t ∂timeMeasure,
      weightedRate (positiveCoeff multiplier) S.activity t ≤
        weightedRate (fun j => (α j : ℝ)) (fun j t => t * S.activity j t) t +
        ENNReal.ofReal (r t) + weightedRate (negativeCoeff multiplier) S.activity t := by
    filter_upwards [hS.binary, ae_time_nonneg, hr_nonneg, hmajor] with t hb ht hr₀ hbnd
    obtain ⟨hleft, hright⟩ := rate_conversion S α multiplier ht (binary_nonneg hb) hα hr₀
    rw [← hleft, ← hright]
    apply ENNReal.ofReal_le_ofReal
    rw [score_balance S α multiplier t] at hbnd
    linarith
  have hi := lintegral_mono_ae hp
  rw [lintegral_add_three (weightedRate_measurable (momentRate_measurable S)) hr.ennreal_ofReal,
    lintegral_workRate hS, lintegral_costRate, lintegral_workRate hS] at hi
  exact hi

/-- The nonnegative part of the usual signed dual lower bound. -/
theorem dual_lower_bound {m : ℕ} {p α multiplier : Fin n → ℚ}
    {S : MeasurableSchedule n} {r : ℝ → ℝ}
    (hS : S.Feasible m p) (hα : ∀ j, 0 ≤ (α j : ℝ))
    (hr : Measurable r) (hr_nonneg : ∀ᵐ t ∂timeMeasure, 0 ≤ r t)
    (hmajor : ∀ᵐ t ∂timeMeasure,
      scoreValue (score α multiplier t) (fun j => S.activity j t) ≤ r t) :
    dualPositiveWork multiplier p -
      ((∫⁻ t, ENNReal.ofReal (r t) ∂timeMeasure) + dualNegativeWork multiplier p) ≤ S.cost α := by
  apply tsub_le_iff_right.mpr
  simpa only [add_assoc] using dual_lower_bound_additive hS hα hr hr_nonneg hmajor

/-- Attainment of a nonnegative measurable support witness gives exact dual equality. -/
theorem dual_eq_of_ae_score_eq {m : ℕ} {p α multiplier : Fin n → ℚ}
    {S : MeasurableSchedule n} {r : ℝ → ℝ}
    (hS : S.Feasible m p) (hα : ∀ j, 0 ≤ (α j : ℝ))
    (hr : Measurable r) (hr_nonneg : ∀ᵐ t ∂timeMeasure, 0 ≤ r t)
    (htight : ∀ᵐ t ∂timeMeasure,
      scoreValue (score α multiplier t) (fun j => S.activity j t) = r t) :
    dualPositiveWork multiplier p =
      S.cost α + (∫⁻ t, ENNReal.ofReal (r t) ∂timeMeasure) +
        dualNegativeWork multiplier p := by
  have hp : ∀ᵐ t ∂timeMeasure,
      weightedRate (positiveCoeff multiplier) S.activity t =
        weightedRate (fun j => (α j : ℝ)) (fun j t => t * S.activity j t) t +
          ENNReal.ofReal (r t) + weightedRate (negativeCoeff multiplier) S.activity t := by
    filter_upwards [hS.binary, ae_time_nonneg, hr_nonneg, htight] with t hb ht hr₀ heq
    obtain ⟨hleft, hright⟩ := rate_conversion S α multiplier ht (binary_nonneg hb) hα hr₀
    rw [← hleft, ← hright]
    congr 1
    rw [score_balance S α multiplier t] at heq
    linarith
  have hi := lintegral_congr_ae hp
  rw [lintegral_add_three (weightedRate_measurable (momentRate_measurable S)) hr.ennreal_ofReal,
    lintegral_workRate hS, lintegral_costRate, lintegral_workRate hS] at hi
  exact hi

/-- An attained integrated dual lower bound certifies optimality even on the half-line. -/
theorem optimal_of_exact_dual {m : ℕ} {p α multiplier : Fin n → ℚ}
    {candidate competitor : MeasurableSchedule n} {r : ℝ → ℝ}
    (_hc : candidate.Feasible m p) (ht : competitor.Feasible m p)
    (hα : ∀ j, 0 ≤ (α j : ℝ))
    (hr : Measurable r) (hr_nonneg : ∀ᵐ t ∂timeMeasure, 0 ≤ r t)
    (hmajor : ∀ᵐ t ∂timeMeasure,
      scoreValue (score α multiplier t) (fun j => competitor.activity j t) ≤ r t)
    (heq :
      dualPositiveWork multiplier p =
        candidate.cost α + (∫⁻ t, ENNReal.ofReal (r t) ∂timeMeasure) +
          dualNegativeWork multiplier p) :
    candidate.cost α ≤ competitor.cost α := by
  have hfinite : (∫⁻ t, ENNReal.ofReal (r t) ∂timeMeasure) + dualNegativeWork multiplier p ≠ ⊤ := by
    have h := dualPositiveWork_ne_top multiplier p
    rw [heq, add_assoc] at h
    exact (ENNReal.add_ne_top.mp h).2
  apply (ENNReal.add_le_add_iff_right hfinite).mp
  rw [← add_assoc, ← heq, ← add_assoc]
  exact dual_lower_bound_additive ht hα hr hr_nonneg hmajor

/-- Equal required workloads turn pointwise affine-score dominance into global
cost optimality. Comparison is over the entire nonnegative time domain, and
no finite-cost assumption is imposed on the competitor. -/
theorem optimal_of_ae_score_le {m : ℕ} {p α multiplier : Fin n → ℚ}
    {candidate competitor : MeasurableSchedule n}
    (hc : candidate.Feasible m p) (ht : competitor.Feasible m p)
    (hα : ∀ j, 0 ≤ (α j : ℝ))
    (hscore : ∀ᵐ t ∂timeMeasure,
      scoreValue (score α multiplier t) (fun j => competitor.activity j t) ≤
        scoreValue (score α multiplier t) (fun j => candidate.activity j t)) :
    candidate.cost α ≤ competitor.cost α := by
  have hp : ∀ᵐ t ∂timeMeasure,
      weightedRate (positiveCoeff multiplier) competitor.activity t +
        weightedRate (fun j => (α j : ℝ)) (fun j t => t * candidate.activity j t) t +
        weightedRate (negativeCoeff multiplier) candidate.activity t ≤
      weightedRate (positiveCoeff multiplier) candidate.activity t +
        weightedRate (fun j => (α j : ℝ)) (fun j t => t * competitor.activity j t) t +
        weightedRate (negativeCoeff multiplier) competitor.activity t := by
    filter_upwards [hc.binary, ht.binary, ae_time_nonneg, hscore] with t hb_c hb_t htime h
    have huc : ∀ j, 0 ≤ candidate.activity j t := binary_nonneg hb_c
    have hut : ∀ j, 0 ≤ competitor.activity j t := binary_nonneg hb_t
    have hmc : ∀ j, 0 ≤ t * candidate.activity j t := fun j => mul_nonneg htime (huc j)
    have hmt : ∀ j, 0 ≤ t * competitor.activity j t := fun j => mul_nonneg htime (hut j)
    rw [score_balance competitor α multiplier t, score_balance candidate α multiplier t] at h
    have hreal :
        (∑ j, positiveCoeff multiplier j * competitor.activity j t) +
        (∑ j, (α j : ℝ) * (t * candidate.activity j t)) +
          (∑ j, negativeCoeff multiplier j * candidate.activity j t) ≤
        (∑ j, positiveCoeff multiplier j * candidate.activity j t) +
        (∑ j, (α j : ℝ) * (t * competitor.activity j t)) +
          (∑ j, negativeCoeff multiplier j * competitor.activity j t) := by linarith
    have hpc : 0 ≤ ∑ j, positiveCoeff multiplier j * candidate.activity j t :=
      Finset.sum_nonneg fun j _ => mul_nonneg (positiveCoeff_nonneg multiplier j) (huc j)
    have hpt : 0 ≤ ∑ j, positiveCoeff multiplier j * competitor.activity j t :=
      Finset.sum_nonneg fun j _ => mul_nonneg (positiveCoeff_nonneg multiplier j) (hut j)
    have hcc : 0 ≤ ∑ j, (α j : ℝ) * (t * candidate.activity j t) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hα j) (hmc j)
    have hct : 0 ≤ ∑ j, (α j : ℝ) * (t * competitor.activity j t) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hα j) (hmt j)
    have hnc : 0 ≤ ∑ j, negativeCoeff multiplier j * candidate.activity j t :=
      Finset.sum_nonneg fun j _ => mul_nonneg (negativeCoeff_nonneg multiplier j) (huc j)
    have hnt : 0 ≤ ∑ j, negativeCoeff multiplier j * competitor.activity j t :=
      Finset.sum_nonneg fun j _ => mul_nonneg (negativeCoeff_nonneg multiplier j) (hut j)
    have hx := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_add (add_nonneg hpt hcc) hnc, ENNReal.ofReal_add hpt hcc,
      ENNReal.ofReal_add (add_nonneg hpc hct) hnt, ENNReal.ofReal_add hpc hct,
      ofReal_weighted_sum (f := competitor.activity) (t := t) (positiveCoeff_nonneg multiplier) hut,
      ofReal_weighted_sum (f := fun j t => t * candidate.activity j t) (t := t) hα hmc,
      ofReal_weighted_sum (f := candidate.activity) (t := t) (negativeCoeff_nonneg multiplier) huc,
      ofReal_weighted_sum (f := candidate.activity) (t := t) (positiveCoeff_nonneg multiplier) huc,
      ofReal_weighted_sum (f := fun j t => t * competitor.activity j t) (t := t) hα hmt,
      ofReal_weighted_sum (f := competitor.activity) (t := t) (negativeCoeff_nonneg multiplier) hut] at hx
    exact hx
  have hi := lintegral_mono_ae hp
  rw [lintegral_add_three (weightedRate_measurable competitor.measurable_activity)
      (weightedRate_measurable (momentRate_measurable candidate)),
    lintegral_add_three (weightedRate_measurable candidate.measurable_activity)
      (weightedRate_measurable (momentRate_measurable competitor)),
    lintegral_workRate ht, lintegral_costRate, lintegral_workRate hc,
    lintegral_workRate hc, lintegral_costRate, lintegral_workRate ht] at hi
  have hfinite : dualPositiveWork multiplier p + dualNegativeWork multiplier p ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨dualPositiveWork_ne_top multiplier p, dualNegativeWork_ne_top multiplier p⟩
  apply (ENNReal.add_le_add_iff_right hfinite).mp
  change candidate.cost α + (dualPositiveWork multiplier p + dualNegativeWork multiplier p) ≤
    competitor.cost α + (dualPositiveWork multiplier p + dualNegativeWork multiplier p)
  simpa only [dualPositiveWork, dualNegativeWork, add_comm, add_left_comm, add_assoc] using hi

end TBB
