import TBB.CheckerCore
import TBB.Bridge
import TBB.Optimality

open MeasureTheory
open scoped ENNReal BigOperators

namespace TBB

theorem CoversFrom.covers {S : Schedule n m} {a b : ℚ} (h : CoversFrom a S b)
    {t : ℝ} (ha : (a : ℝ) ≤ t) (hb : t < (b : ℝ)) :
    ∃ I ∈ S, (I.start : ℝ) ≤ t ∧ t < (I.stop : ℝ) := by
  induction S generalizing a with
  | nil =>
    change a = b at h
    rw [h] at ha
    exact (not_lt_of_ge ha hb).elim
  | cons I tail ih =>
    change a = I.start ∧ I.start < I.stop ∧ CoversFrom I.stop tail b at h
    by_cases hI : t < (I.stop : ℝ)
    · exact ⟨I, by simp, by simpa only [← h.1] using ha, hI⟩
    · obtain ⟨J, hJ, hjl, hjr⟩ := ih h.2.2 (le_of_not_gt hI)
      exact ⟨J, List.mem_cons_of_mem _ hJ, hjl, hjr⟩

theorem endpointPass.real {c : Certificate n m} {I : Phase n m} {t μ : ℚ}
    (h : endpointPass c I t μ) :
    0 ≤ (μ : ℝ) ∧
      scoreValue (score c.alpha c.multiplier t) (fun j => if I.active j then 1 else 0) =
        thresholdBound m (score c.alpha c.multiplier t) μ := by
  rcases h with ⟨hpos, htight⟩
  refine ⟨by exact_mod_cast hpos, ?_⟩
  have hcast := congrArg (fun x : ℚ => (x : ℝ)) htight
  simpa only [Phase.rationalScoreValue, rationalThreshold, rationalScore, scoreValue, score,
    thresholdBound, Rat.cast_sum, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_max,
    Rat.cast_zero, Rat.cast_one, Rat.cast_natCast, apply_ite] using hcast

/-- Endpoint tightness and the tail condition dominate every feasible rate at every
nonnegative time, including times after the certificate horizon. -/
theorem Certificate.Passes.score_compare {c : Certificate n m} (h : c.Passes)
    {t : ℝ} (ht : 0 ≤ t) {u : Fin n → ℝ} (hrate : RateFeasible m u) :
    scoreValue (score c.alpha c.multiplier t) u ≤
      scoreValue (score c.alpha c.multiplier t) (fun j => c.schedule.toMeasurable.activity j t) := by
  have hvalid := h.valid
  have checks := h
  rcases checks with ⟨_, _, _, hcovered, _, hperJob, _, _⟩
  by_cases hh : t < (c.horizon : ℝ)
  · obtain ⟨I, hI, hstart, hstop⟩ := hcovered.covers (by simpa using ht) hh
    obtain ⟨μa, μb, ha, hb⟩ := h.endpoint_witnesses hI
    have heq : (fun j => c.schedule.toMeasurable.activity j t) =
        fun j => if I.active j then 1 else 0 :=
      funext fun j => Schedule.activity_eq_phase hvalid hI ⟨hstart, hstop⟩ j
    rw [heq]
    exact threshold_optimal_between hstart hstop.le hrate ha.real.1 hb.real.1 ha.real.2 hb.real.2
  · have htailTime : (c.horizon : ℝ) ≤ t := le_of_not_gt hh
    have htal : ∀ j, score c.alpha c.multiplier c.horizon j ≤ 0 := by
      intro j
      obtain ⟨_, _, _, _, hr⟩ := hperJob j
      unfold rationalScore at hr
      unfold score
      exact_mod_cast hr
    have hac : ∀ j, 0 ≤ (c.alpha j : ℝ) := by
      intro j
      exact_mod_cast (hperJob j).2.1.le
    have hzero : (fun j => c.schedule.toMeasurable.activity j t) = fun _ => 0 := by
      funext j
      apply Schedule.activity_zero_of_no_phase
      intro I hI htI
      have hIh : (I.stop : ℝ) ≤ (c.horizon : ℝ) := by exact_mod_cast (hvalid.bounds I hI).2.2
      exact (not_lt_of_ge (le_trans hIh htailTime)) htI.2
    rw [hzero]
    exact tail_optimal htailTime hac htal hrate

/-- The accepted phase assignments realize the actual support function on the half-line. -/
theorem Certificate.Passes.support_eq {c : Certificate n m} (h : c.Passes)
    {t : ℝ} (ht : 0 ≤ t) :
    supportFunction m (score c.alpha c.multiplier t) =
      scoreValue (score c.alpha c.multiplier t) (fun j => c.schedule.toMeasurable.activity j t) := by
  have hrate := rateFeasible_of_binary_capacity (Schedule.activity_binary h.valid t)
    (Schedule.activity_capacity h.valid t)
  refine le_antisymm ?_ (score_le_support hrate)
  unfold supportFunction
  apply csSup_le
  · exact ⟨_, _, hrate, rfl⟩
  · rintro r ⟨u, hu, rfl⟩
    exact h.score_compare ht hu

/-- Every feasible measurable competitor satisfies the accepted score comparison almost
everywhere, with no horizon restriction on the competitor. -/
theorem Certificate.Passes.ae_score_compare {c : Certificate n m} (h : c.Passes)
    {U : MeasurableSchedule n} (hu : U.Feasible m c.work) :
    ∀ᵐ t ∂timeMeasure,
      scoreValue (score c.alpha c.multiplier t) (fun j => U.activity j t) ≤
        scoreValue (score c.alpha c.multiplier t) (fun j => c.schedule.toMeasurable.activity j t) := by
  filter_upwards [ae_time_nonneg, hu.binary, hu.capacity] with t ht hb hc
  exact h.score_compare ht (rateFeasible_of_binary_capacity hb hc)

/-- The score of the proposed schedule is an explicit measurable support witness. -/
noncomputable def Certificate.supportWitness (c : Certificate n m) (t : ℝ) : ℝ :=
  scoreValue (score c.alpha c.multiplier t) (fun j => c.schedule.toMeasurable.activity j t)

theorem Certificate.supportWitness_measurable (c : Certificate n m) :
    Measurable c.supportWitness :=
  measurable_schedule_score c.schedule.toMeasurable c.alpha c.multiplier

theorem Certificate.Passes.supportWitness_nonneg {c : Certificate n m} (h : c.Passes) :
    ∀ᵐ t ∂timeMeasure, 0 ≤ c.supportWitness t := by
  filter_upwards [ae_time_nonneg] with t ht
  have hzero : RateFeasible m (fun _ : Fin n => 0) := by
    refine ⟨fun _ => ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp
  simpa only [Certificate.supportWitness, scoreValue, mul_zero, Finset.sum_const_zero]
    using h.score_compare ht hzero

theorem Certificate.Passes.witness_dual_eq {c : Certificate n m} (h : c.Passes) :
    dualPositiveWork c.multiplier c.work =
      c.schedule.toMeasurable.cost c.alpha +
        (∫⁻ t, ENNReal.ofReal (c.supportWitness t) ∂timeMeasure) +
          dualNegativeWork c.multiplier c.work := by
  have checks := h
  rcases checks with ⟨_, _, _, _, _, hj, _, _⟩
  have hw : ∀ j, c.schedule.work j = c.work j := fun j => (hj j).2.2.1
  have hα : ∀ j, 0 ≤ (c.alpha j : ℝ) := by
    intro j
    exact_mod_cast (hj j).2.1.le
  exact dual_eq_of_ae_score_eq (Schedule.toMeasurable_feasible h.valid hw) hα
    c.supportWitness_measurable h.supportWitness_nonneg (Filter.Eventually.of_forall fun _ => rfl)

/-- Acceptance proves equality in the integrated dual bound for the exact support function. -/
theorem Certificate.Passes.integrated_dual {c : Certificate n m} (h : c.Passes) :
    dualPositiveWork c.multiplier c.work =
      c.schedule.toMeasurable.cost c.alpha +
        (∫⁻ t, ENNReal.ofReal (supportFunction m (score c.alpha c.multiplier t)) ∂timeMeasure) +
          dualNegativeWork c.multiplier c.work := by
  have heq : (∫⁻ t, ENNReal.ofReal (supportFunction m (score c.alpha c.multiplier t)) ∂timeMeasure) =
      ∫⁻ t, ENNReal.ofReal (c.supportWitness t) ∂timeMeasure := by
    apply lintegral_congr_ae
    filter_upwards [ae_time_nonneg] with t ht
    exact congrArg ENNReal.ofReal (h.support_eq ht)
  rw [heq]
  exact h.witness_dual_eq

private theorem phase_sum_score_integral (S : Schedule n m)
    (α lam : Fin n → ℚ) :
    (S.map fun I => ∑ j, (lam j * I.work j - α j * I.moment j)).sum =
      (∑ j, lam j * S.work j) - S.cost α := by
  induction S with
  | nil => simp [Schedule.work, Schedule.cost, Schedule.moment]
  | cons I S ih =>
    simp only [List.map_cons, List.sum_cons, ih, Schedule.work, Schedule.cost, Schedule.moment]
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring

theorem Certificate.scoreIntegral_eq (c : Certificate n m) :
    c.scoreIntegral = (∑ j, c.multiplier j * c.schedule.work j) - c.schedule.cost c.alpha :=
  phase_sum_score_integral c.schedule c.alpha c.multiplier

/-- The rational score integral computed by the checker agrees exactly with the
integral of the support function in the mathematical dual bound. -/
theorem Certificate.Passes.support_integral_eq {c : Certificate n m} (h : c.Passes) :
    let J := ∫⁻ t, ENNReal.ofReal (supportFunction m (score c.alpha c.multiplier t)) ∂timeMeasure
    J ≠ ⊤ ∧ J.toReal = (c.scoreIntegral : ℝ) := by
  let J := ∫⁻ t, ENNReal.ofReal (supportFunction m (score c.alpha c.multiplier t)) ∂timeMeasure
  change J ≠ ⊤ ∧ J.toReal = _
  have hdual := h.integrated_dual
  change dualPositiveWork c.multiplier c.work = c.schedule.toMeasurable.cost c.alpha + J +
    dualNegativeWork c.multiplier c.work at hdual
  have hfinite := dualPositiveWork_ne_top c.multiplier c.work
  rw [hdual] at hfinite
  rcases ENNReal.add_ne_top.mp hfinite with ⟨hsum, hneg⟩
  rcases ENNReal.add_ne_top.mp hsum with ⟨hcostFinite, hJ⟩
  have hdualReal := congrArg ENNReal.toReal hdual
  rw [ENNReal.toReal_add hsum hneg, ENNReal.toReal_add hcostFinite hJ] at hdualReal
  have checks := h
  rcases checks with ⟨_, _, _, _, _, hj, _, _⟩
  have hα : ∀ j, 0 ≤ c.alpha j := fun j => (hj j).2.1.le
  have hwork : ∀ j, c.schedule.work j = c.work j := fun j => (hj j).2.2.1
  have hp : ∀ j, 0 ≤ (c.work j : ℝ) := by
    intro j
    exact_mod_cast (hj j).1.le
  have hcostRat : 0 ≤ c.schedule.cost c.alpha :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hα j) (Schedule.moment_nonneg h.valid j)
  have hcostReal : 0 ≤ (c.schedule.cost c.alpha : ℝ) := by exact_mod_cast hcostRat
  rw [Schedule.toMeasurable_cost h.valid hα, ENNReal.toReal_ofReal hcostReal] at hdualReal
  have hworkReal := dual_work_diff_toReal c.multiplier c.work hp
  have hscoreReal : (c.scoreIntegral : ℝ) =
      (((∑ j, c.multiplier j * c.work j) : ℚ) : ℝ) - (c.schedule.cost c.alpha : ℝ) := by
    rw [c.scoreIntegral_eq, Rat.cast_sub]
    simp only [hwork]
  have hJReal : J.toReal = (c.scoreIntegral : ℝ) := by linarith
  exact ⟨hJ, hJReal⟩

/-- The accepted schedule is executable and feasible, represents the claimed moments and
objective, and is optimal over arbitrary measurable competitors on the half-line. -/
structure Certificate.Sound (c : Certificate n m) : Prop where
  valid : c.schedule.ValidAt c.horizon
  feasible : c.schedule.toMeasurable.Feasible m c.work
  moments : ∀ j, c.schedule.toMeasurable.moment j =
    ENNReal.ofReal (c.individualMoments j : ℝ)
  objective : c.schedule.toMeasurable.cost c.alpha = ENNReal.ofReal (c.objective : ℝ)
  optimal : ∀ U : MeasurableSchedule n, U.Feasible m c.work →
    c.schedule.toMeasurable.cost c.alpha ≤ U.cost c.alpha

theorem Certificate.Passes.sound {c : Certificate n m} (h : c.Passes) : c.Sound := by
  have hv := h.valid
  have checks := h
  rcases checks with ⟨_, _, _, _, _, hj, hvalue, _⟩
  have hw : ∀ j, c.schedule.work j = c.work j := fun j => (hj j).2.2.1
  have hα : ∀ j, 0 < c.alpha j := fun j => (hj j).2.1
  have hf := Schedule.toMeasurable_feasible hv hw
  have hcost := Schedule.toMeasurable_cost hv (fun j => (hα j).le)
  refine ⟨hv, hf, ?_, ?_, ?_⟩
  · intro j
    rw [Schedule.toMeasurable_moment hv, (hj j).2.2.2.1]
  · rw [hcost, hvalue]
  · intro U hu
    exact optimal_of_exact_dual hf hu (by intro j; exact_mod_cast (hα j).le)
      c.supportWitness_measurable h.supportWitness_nonneg
      (h.ae_score_compare hu) h.witness_dual_eq

/-- In particular soundness includes Lebesgue measurable activities represented up to
null sets, without imposing a finite horizon or finite integral on the competitors. -/
theorem Certificate.Sound.optimal_aeActivity {c : Certificate n m} (hs : c.Sound)
    (u : Fin n → ℝ → ℝ) (hu : ∀ j, AEMeasurable (u j) timeMeasure)
    (hb : ∀ᵐ t ∂timeMeasure, ∀ j, u j t = 0 ∨ u j t = 1)
    (hc : ∀ᵐ t ∂timeMeasure, ∑ j, u j t ≤ (m : ℝ))
    (hw : ∀ j, (∫⁻ t, ENNReal.ofReal (u j t) ∂timeMeasure) =
      ENNReal.ofReal (c.work j : ℝ)) :
    c.schedule.toMeasurable.cost c.alpha ≤
      ∑ j, ENNReal.ofReal (c.alpha j : ℝ) *
        (∫⁻ t, ENNReal.ofReal (t * u j t) ∂timeMeasure) := by
  rw [← MeasurableSchedule.ofAEActivity_cost u hu c.alpha]
  exact hs.optimal _ (MeasurableSchedule.ofAEActivity_feasible u hu hb hc hw)

/-- A successful executable run implies full mathematical certification of the decoded
schedule, including unrestricted optimality. -/
theorem check_sound {raw : RawCertificate} (h : check raw = true) :
    ∃ c : Certificate raw.n raw.m, raw.decode = some c ∧ c.Sound := by
  obtain ⟨c, hd, hp⟩ := (check_iff raw).mp h
  exact ⟨c, hd, hp.sound⟩

end TBB
