import TBB.Measurable
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

open MeasureTheory
open scoped ENNReal BigOperators

namespace TBB

/-- Machine labels in the original model. Each machine has one state at each time.
No job has two machine labels at almost every nonnegative time. -/
structure LabeledSchedule (n m : ℕ) where
  assigned : Fin m → ℝ → Option (Fin n)
  measurableJob : ∀ k j, MeasurableSet {t | assigned k t = some j}
  exclusive : ∀ᵐ t ∂timeMeasure, ∀ k k' j,
    assigned k t = some j → assigned k' t = some j → k = k'

namespace LabeledSchedule

variable {n m : ℕ}

noncomputable def toActivity (S : LabeledSchedule n m) : MeasurableSchedule n where
  activity j t := if ∃ k, S.assigned k t = some j then 1 else 0
  measurable_activity j := by
    classical
    have h : MeasurableSet {t | ∃ k, S.assigned k t = some j} := by
      rw [Set.setOf_exists]
      exact MeasurableSet.iUnion (fun k => S.measurableJob k j)
    exact measurable_const.piecewise h measurable_const

private theorem active_card_le (f : Fin m → Option (Fin n)) :
    (Finset.univ.filter (fun j => ∃ k, f k = some j)).card ≤ m := by
  classical
  let A := Finset.univ.filter (fun j => ∃ k, f k = some j)
  have hsub : A.image some ⊆ Finset.univ.image f := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    rcases (Finset.mem_filter.mp hj).2 with ⟨k, hk⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  calc
    A.card = (A.image some).card :=
      (Finset.card_image_of_injective A (fun _ _ h => Option.some.inj h)).symm
    _ ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    _ = m := by simp

theorem toActivity_feasible (S : LabeledSchedule n m) (p : Fin n → ℚ)
    (workload : ∀ j, S.toActivity.work j = ENNReal.ofReal (p j : ℝ)) :
    S.toActivity.Feasible m p := by
  classical
  refine ⟨Filter.Eventually.of_forall ?_, Filter.Eventually.of_forall ?_, workload⟩
  · intro t j
    change (if ∃ k, S.assigned k t = some j then (1 : ℝ) else 0) = 0 ∨
      (if ∃ k, S.assigned k t = some j then (1 : ℝ) else 0) = 1
    split_ifs <;> simp
  · intro t
    change ∑ j, (if ∃ k, S.assigned k t = some j then (1 : ℝ) else 0) ≤ (m : ℝ)
    rw [Finset.sum_boole]
    exact_mod_cast active_card_le (fun k => S.assigned k t)

end LabeledSchedule

namespace MeasurableSchedule

variable {n m : ℕ}

noncomputable def activeJobs (S : MeasurableSchedule n) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => S.activity j t = 1)

private theorem mem_activeJobs (S : MeasurableSchedule n) (t : ℝ) (j : Fin n) :
    j ∈ S.activeJobs t ↔ S.activity j t = 1 := by
  classical
  simp [activeJobs]

private theorem measurable_activeJobs_fiber (S : MeasurableSchedule n)
    (A : Finset (Fin n)) : MeasurableSet {t | S.activeJobs t = A} := by
  classical
  have heq : {t | S.activeJobs t = A} =
      ⋂ j : Fin n, {t | S.activity j t = 1 ↔ j ∈ A} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h j
      rw [← mem_activeJobs, h]
    · intro h
      exact Finset.ext (fun j => (S.mem_activeJobs t j).trans (h j))
  rw [heq]
  refine MeasurableSet.iInter fun j => ?_
  have hbase : MeasurableSet {t | S.activity j t = 1} :=
    (S.measurable_activity j) (measurableSet_singleton 1)
  by_cases hj : j ∈ A
  · simpa [hj] using hbase
  · have hs : {t | S.activity j t = 1 ↔ j ∈ A} = {t | S.activity j t = 1}ᶜ := by
      ext t
      simp only [hj, iff_false, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [hs]
    exact hbase.compl

/-- The k-th active job in job-index order, with idle if that index is out of range. -/
private def label (A : Finset (Fin n)) (k : Fin m) : Option (Fin n) :=
  if h : k.val < A.card then some ((A.orderIsoOfFin rfl ⟨k.val, h⟩).val) else none

private theorem label_exclusive (A : Finset (Fin n)) (k k' : Fin m) (j : Fin n)
    (h : label A k = some j) (h' : label A k' = some j) : k = k' := by
  unfold label at h h'
  split at h <;> (try contradiction)
  split at h' <;> (try contradiction)
  rename_i hk hk'
  injection h with h
  injection h' with h'
  have heq : A.orderIsoOfFin rfl (⟨k.val, hk⟩ : Fin A.card) =
      A.orderIsoOfFin rfl (⟨k'.val, hk'⟩ : Fin A.card) :=
    Subtype.ext (h.trans h'.symm)
  exact Fin.ext (congrArg (fun i : Fin A.card => i.val) ((A.orderIsoOfFin rfl).injective heq))

private theorem label_iff (A : Finset (Fin n)) (hcap : A.card ≤ m) (j : Fin n) :
    (∃ k : Fin m, label A k = some j) ↔ j ∈ A := by
  constructor
  · rintro ⟨k, hk⟩
    unfold label at hk
    split at hk <;> (try contradiction)
    rename_i h
    injection hk with he
    rw [← he]
    exact (A.orderIsoOfFin rfl (⟨k.val, h⟩ : Fin A.card)).property
  · intro hj
    let r : Fin A.card := (A.orderIsoOfFin rfl).symm ⟨j, hj⟩
    let k : Fin m := ⟨r.val, lt_of_lt_of_le r.isLt hcap⟩
    refine ⟨k, ?_⟩
    unfold label
    rw [dif_pos r.isLt]
    exact congrArg (fun x : ↥A => some x.val) ((A.orderIsoOfFin rfl).apply_symm_apply ⟨j, hj⟩)

noncomputable def labeled (S : MeasurableSchedule n) (m : ℕ) : LabeledSchedule n m where
  assigned k t := label (S.activeJobs t) k
  measurableJob k j := by
    classical
    have heq : {t | label (S.activeJobs t) k = some j} =
        ⋃ A : Finset (Fin n), if label A k = some j then {t | S.activeJobs t = A} else ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨S.activeJobs t, by simp [h]⟩
      · rintro ⟨A, h⟩
        split at h
        · have ht : S.activeJobs t = A := h
          rwa [ht]
        · exact False.elim h
    rw [heq]
    refine MeasurableSet.iUnion fun A => ?_
    split
    · exact S.measurable_activeJobs_fiber A
    · exact MeasurableSet.empty
  exclusive := Filter.Eventually.of_forall fun t k k' j =>
    label_exclusive (S.activeJobs t) k k' j

private theorem card_activeJobs_le (S : MeasurableSchedule n) (t : ℝ)
    (hb : ∀ j, S.activity j t = 0 ∨ S.activity j t = 1)
    (hc : ∑ j, S.activity j t ≤ (m : ℝ)) : (S.activeJobs t).card ≤ m := by
  classical
  have h : (∑ j, S.activity j t) =
      ∑ j, (if S.activity j t = 1 then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    rcases hb j with hj | hj <;> simp [hj]
  rw [h, Finset.sum_boole] at hc
  exact_mod_cast hc

/-- The finite-capacity binary activity model retains all measurable labeled schedules
up to changes on null sets. -/
theorem labeled_activity_ae (S : MeasurableSchedule n) {p : Fin n → ℚ}
    (h : S.Feasible m p) (j : Fin n) :
    (S.labeled m).toActivity.activity j =ᵐ[timeMeasure] S.activity j := by
  classical
  filter_upwards [h.binary, h.capacity] with t hb hc
  have he := label_iff (S.activeJobs t) (S.card_activeJobs_le t hb hc) j
  change (if ∃ k : Fin m, label (S.activeJobs t) k = some j then 1 else 0) =
    S.activity j t
  have hiff := he.trans (S.mem_activeJobs t j)
  rcases hb j with hj | hj
  · have hnot : ¬ ∃ k : Fin m, label (S.activeJobs t) k = some j := by
      rw [hiff, hj]
      norm_num
    simp [hnot, hj]
  · simp [hiff.mpr hj, hj]

theorem labeled_feasible (S : MeasurableSchedule n) {p : Fin n → ℚ}
    (h : S.Feasible m p) : (S.labeled m).toActivity.Feasible m p := by
  apply LabeledSchedule.toActivity_feasible
  intro j
  rw [← h.workload j]
  apply lintegral_congr_ae
  filter_upwards [S.labeled_activity_ae h j] with t ht
  rw [ht]

theorem labeled_same_cost (S : MeasurableSchedule n) {p : Fin n → ℚ}
    (h : S.Feasible m p) (α : Fin n → ℚ) : (S.labeled m).toActivity.cost α = S.cost α := by
  unfold MeasurableSchedule.cost
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply lintegral_congr_ae
  filter_upwards [S.labeled_activity_ae h j] with t ht
  rw [ht]

end MeasurableSchedule
end TBB
