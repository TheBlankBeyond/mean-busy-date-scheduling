import TBB.Machines
import TBB.Bridge
import TBB.Realization

open MeasureTheory
open scoped ENNReal BigOperators

namespace TBB

namespace Operation

variable {n m : ℕ}

def timeSet (op : Operation n) : Set ℝ := Set.Ico (op.start : ℝ) (op.stop : ℝ)

private theorem separated_not_both {a b : Operation n} {t : ℝ}
    (h : a.Separated b) (ha : t ∈ a.timeSet) (hb : t ∈ b.timeSet) : False := by
  rcases h with h | h
  · have h' : (a.stop : ℝ) ≤ (b.start : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (h'.trans hb.1)) ha.2
  · have h' : (b.stop : ℝ) ≤ (a.start : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (h'.trans ha.1)) hb.2

/-- Per-record bounds and pairwise constraints for an operation list. -/
structure Valid (ops : List (Operation n)) (m : ℕ) : Prop where
  pairwise : ops.Pairwise Compatible
  bounds : ∀ op ∈ ops, 0 ≤ op.start ∧ op.start < op.stop ∧ op.machine < m

private theorem equal_of_acting {ops : List (Operation n)} (h : ops.Pairwise Compatible)
    {a b : Operation n} (ha : a ∈ ops) (hb : b ∈ ops) {t : ℝ}
    (hat : t ∈ a.timeSet) (hbt : t ∈ b.timeSet)
    (hc : a.machine = b.machine ∨ a.job = b.job) : a = b := by
  induction ops with
  | nil => simp at ha
  | cons c ops ih =>
    have hp := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with hac | haTail
    · subst a
      rcases List.mem_cons.mp hb with hbc | hbTail
      · exact hbc.symm
      · exact (separated_not_both (hp.1 b hbTail hc) hat hbt).elim
    · rcases List.mem_cons.mp hb with hbc | hbTail
      · subst b
        have hswap : c.machine = a.machine ∨ c.job = a.job :=
          hc.elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)
        exact (separated_not_both (hp.1 a haTail hswap) hbt hat).elim
      · exact ih hp.2 haTail hbTail

private noncomputable def assigned (ops : List (Operation n)) (k : Fin m) (t : ℝ) :
    Option (Fin n) := by
  classical
  exact if ht : ∃ op ∈ ops, op.machine = k.val ∧ t ∈ op.timeSet
    then some (Classical.choose ht).job else none

private theorem assigned_iff {ops : List (Operation n)} (h : ops.Pairwise Compatible)
    (k : Fin m) (j : Fin n) (t : ℝ) :
    assigned ops k t = some j ↔
      ∃ op ∈ ops, op.machine = k.val ∧ t ∈ op.timeSet ∧ op.job = j := by
  classical
  unfold assigned
  split
  · rename_i he
    let chosen := Classical.choose he
    have hc := Classical.choose_spec he
    change chosen ∈ ops ∧ chosen.machine = k.val ∧ t ∈ chosen.timeSet at hc
    change some chosen.job = some j ↔ _
    constructor
    · intro hj
      exact ⟨chosen, hc.1, hc.2.1, hc.2.2, Option.some.inj hj⟩
    · rintro ⟨op, hop, hk, ht, hj⟩
      have heq := equal_of_acting h hc.1 hop hc.2.2 ht (Or.inl (hc.2.1.trans hk.symm))
      simp [heq, hj]
  · rename_i hn
    constructor
    · simp
    · rintro ⟨op, hop, hk, ht, _⟩
      exact (hn ⟨op, hop, hk, ht⟩).elim

private theorem assignedSet_eq {ops : List (Operation n)} (h : ops.Pairwise Compatible)
    (k : Fin m) (j : Fin n) :
    {t | assigned ops k t = some j} =
      ⋃ i : Fin ops.length, if (ops.get i).machine = k.val ∧ (ops.get i).job = j
        then (ops.get i).timeSet else ∅ := by
  classical
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, assigned_iff h]
  constructor
  · rintro ⟨op, hm, hk, ht, hj⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    refine ⟨i, ?_⟩
    have hlabels : (ops.get i).machine = k.val ∧ (ops.get i).job = j := by
      rw [hi]
      exact ⟨hk, hj⟩
    rw [if_pos hlabels, hi]
    exact ht
  · rintro ⟨i, ht⟩
    split at ht
    · rename_i hc
      exact ⟨ops.get i, List.get_mem _ _, hc.1, ht, hc.2⟩
    · exact False.elim ht

/-- Interpret the exact operation records as their actual machine labels in real time. -/
noncomputable def toLabeled (ops : List (Operation n)) (h : Valid ops m) :
    LabeledSchedule n m where
  assigned := assigned ops
  measurableJob k j := by
    classical
    rw [assignedSet_eq h.pairwise k j]
    refine MeasurableSet.iUnion fun op => ?_
    split
    · exact measurableSet_Ico
    · exact MeasurableSet.empty
  exclusive := by
    apply Filter.Eventually.of_forall
    intro t k k' j ha hb
    obtain ⟨a, ha, hka, hta, hja⟩ := (assigned_iff h.pairwise k j t).mp ha
    obtain ⟨b, hb, hkb, htb, hjb⟩ := (assigned_iff h.pairwise k' j t).mp hb
    have hab := equal_of_acting h.pairwise ha hb hta htb (Or.inr (hja.trans hjb.symm))
    exact Fin.ext (hka.symm.trans (hab ▸ hkb))

/-- A job occupies its recorded machine precisely during an emitted half-open operation. -/
theorem toLabeled_assigned_iff (ops : List (Operation n)) (h : Valid ops m)
    (k : Fin m) (j : Fin n) (t : ℝ) :
    (toLabeled ops h).assigned k t = some j ↔
      ∃ op ∈ ops, op.machine = k.val ∧ t ∈ op.timeSet ∧ op.job = j :=
  assigned_iff h.pairwise k j t

private def singletonPhase (m : ℕ) (op : Operation n) : Phase n m :=
  ⟨op.start, op.stop, if hk : op.machine < m then [(⟨op.machine, hk⟩, op.job)] else []⟩

private theorem singleton_active (op : Operation n) (hk : op.machine < m) (j : Fin n) :
    (singletonPhase m op).active j ↔ op.job = j := by
  simp only [singletonPhase, dif_pos hk, Phase.active, List.map_cons, List.map_nil,
    List.mem_singleton]
  exact eq_comm

open Classical in
private theorem singleton_at (op : Operation n) (hk : op.machine < m) (j : Fin n) (t : ℝ) :
    (singletonPhase m op).realActivity j t =
      if op.job = j ∧ t ∈ op.timeSet then 1 else 0 := by
  classical
  by_cases ht : t ∈ op.timeSet
  · have ht' : t ∈ (singletonPhase m op).timeSet := ht
    rw [Phase.realActivity_at _ _ ht']
    simp [singleton_active op hk j, ht]
  · have ht' : t ∉ (singletonPhase m op).timeSet := ht
    rw [Phase.realActivity_off _ _ ht']
    simp [ht]

open Classical in
private theorem list_activity_eq (ops : List (Operation n))
    (h : ops.Pairwise Compatible) (hk : ∀ op ∈ ops, op.machine < m) (j : Fin n) (t : ℝ) :
    Schedule.realActivity (ops.map (singletonPhase m)) j t =
      if ∃ op ∈ ops, op.job = j ∧ t ∈ op.timeSet then 1 else 0 := by
  classical
  induction ops with
  | nil => simp [Schedule.realActivity]
  | cons op ops ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    change (singletonPhase m op).realActivity j t +
      Schedule.realActivity (ops.map (singletonPhase m)) j t = _
    rw [singleton_at op (hk op (by simp)), ih htail (fun o ho => hk o (by simp [ho]))]
    have he : (∃ o ∈ op :: ops, o.job = j ∧ t ∈ o.timeSet) ↔
        (op.job = j ∧ t ∈ op.timeSet) ∨ (∃ o ∈ ops, o.job = j ∧ t ∈ o.timeSet) := by
      constructor
      · rintro ⟨o, ho, hj, ht⟩
        rcases List.mem_cons.mp ho with rfl | ho
        · exact Or.inl ⟨hj, ht⟩
        · exact Or.inr ⟨o, ho, hj, ht⟩
      · rintro (⟨hj, ht⟩ | ⟨o, ho, hj, ht⟩)
        · exact ⟨op, by simp, hj, ht⟩
        · exact ⟨o, by simp [ho], hj, ht⟩
    rw [if_congr he rfl rfl]
    by_cases ha : op.job = j ∧ t ∈ op.timeSet
    · have hnot : ¬ ∃ o ∈ ops, o.job = j ∧ t ∈ o.timeSet := by
        rintro ⟨o, ho, hj, ht⟩
        exact separated_not_both (hhead o ho (Or.inr (ha.1.trans hj.symm))) ha.2 ht
      simp [ha, hnot]
    · simp [ha]

private theorem labeled_activity_eq (ops : List (Operation n)) (h : Valid ops m) (j : Fin n) :
    (toLabeled ops h).toActivity.activity j = Schedule.realActivity (ops.map (singletonPhase m)) j := by
  classical
  funext t
  rw [list_activity_eq ops h.pairwise (fun o ho => (h.bounds o ho).2.2)]
  change (if ∃ k : Fin m, assigned ops k t = some j then 1 else 0) = _
  have he : (∃ k : Fin m, assigned ops k t = some j) ↔
      ∃ o ∈ ops, o.job = j ∧ t ∈ o.timeSet := by
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨o, ho, _, ht, hj⟩ := (assigned_iff h.pairwise k j t).mp hk
      exact ⟨o, ho, hj, ht⟩
    · rintro ⟨o, ho, hj, ht⟩
      let k : Fin m := ⟨o.machine, (h.bounds o ho).2.2⟩
      exact ⟨k, (assigned_iff h.pairwise k j t).mpr ⟨o, ho, rfl, ht, hj⟩⟩
  exact if_congr he rfl rfl

private theorem singletonWork_map (ops : List (Operation n)) (j : Fin n)
    (hk : ∀ op ∈ ops, op.machine < m) :
    Schedule.work (ops.map (singletonPhase m)) j = operationWork ops j := by
  unfold Schedule.work operationWork operationTally
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun o ho => by
    simp only [Function.comp_def, Phase.work, singleton_active o (hk o ho) j]
    rfl)

private theorem singletonMoment_map (ops : List (Operation n)) (j : Fin n)
    (hk : ∀ op ∈ ops, op.machine < m) :
    Schedule.moment (ops.map (singletonPhase m)) j = operationMoment ops j := by
  unfold Schedule.moment operationMoment operationTally
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun o ho => by
    simp only [Function.comp_def, Phase.moment, singleton_active o (hk o ho) j]
    rfl)

/-- The executable workload sum is the actual half-line Lebesgue workload. -/
theorem toLabeled_work (ops : List (Operation n)) (h : Valid ops m) (j : Fin n) :
    (toLabeled ops h).toActivity.work j = ENNReal.ofReal (operationWork ops j : ℝ) := by
  have hb : ∀ I ∈ ops.map (singletonPhase m), 0 ≤ I.start ∧ I.start ≤ I.stop := by
    intro I hI
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hI
    exact ⟨(h.bounds o ho).1, (h.bounds o ho).2.1.le⟩
  unfold MeasurableSchedule.work
  rw [labeled_activity_eq ops h j]
  change (Schedule.toMeasurable (ops.map (singletonPhase m))).work j = _
  rw [Schedule.toMeasurable_work_aux _ _ hb, singletonWork_map ops j
    (fun o ho => (h.bounds o ho).2.2)]

/-- The executable moment sum is the actual half-line Lebesgue first moment. -/
theorem toLabeled_moment (ops : List (Operation n)) (h : Valid ops m) (j : Fin n) :
    (toLabeled ops h).toActivity.moment j = ENNReal.ofReal (operationMoment ops j : ℝ) := by
  have hb : ∀ I ∈ ops.map (singletonPhase m), 0 ≤ I.start ∧ I.start ≤ I.stop := by
    intro I hI
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hI
    exact ⟨(h.bounds o ho).1, (h.bounds o ho).2.1.le⟩
  unfold MeasurableSchedule.moment
  rw [labeled_activity_eq ops h j]
  change (Schedule.toMeasurable (ops.map (singletonPhase m))).moment j = _
  rw [Schedule.toMeasurable_moment_aux _ _ hb, singletonMoment_map ops j
    (fun o ho => (h.bounds o ho).2.2)]


end Operation

/-- The emitted list denotes a valid assignment on the original time domain. -/
theorem realize_valid {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) :
    Operation.Valid (realize phases) m :=
  ⟨realize_pairwise phases hvalid hjoin, fun _ hop => realize_operation phases hvalid hop⟩

/-- The global workload and first moment of each job are exactly the sums of
its allocation-phase targets, under the Lebesgue interpretation of the emitted records. -/
theorem realize_measurable_totals {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) (j : Fin n) :
    let S := (Operation.toLabeled (realize phases) (realize_valid phases hvalid hjoin)).toActivity
    S.work j = ENNReal.ofReal (((phases.map fun p => (p.stop - p.start) * p.rate j).sum : ℚ) : ℝ) ∧
    S.moment j = ENNReal.ofReal
      (((phases.map fun p => (p.stop ^ 2 - p.start ^ 2) / 2 * p.rate j).sum : ℚ) : ℝ) := by
  dsimp only
  constructor
  · rw [Operation.toLabeled_work, realize_total_work phases hvalid]
  · rw [Operation.toLabeled_moment, realize_total_moment phases hvalid]

private theorem realizePhase_valid {n m : ℕ} (p : AllocationPhase n) (hp : p.Valid m) :
    Operation.Valid p.operations m := by
  obtain ⟨h₀, hab, hz0, hz1, hcap⟩ := hp
  refine ⟨realizePhase_pairwise hab hz0 hz1, ?_⟩
  intro op hop
  obtain ⟨hs, hpos, _, hrow⟩ := realizePhase_operation hab hz0 hz1 hcap hop
  exact ⟨h₀.trans hs, hpos, hrow⟩

/-- Exact Lebesgue interpretation of the schedule on one nonnegative phase. -/
theorem realize_phase_measurable {n m : ℕ} (p : AllocationPhase n) (hp : p.Valid m)
    (j : Fin n) :
    let S := (Operation.toLabeled p.operations (realizePhase_valid p hp)).toActivity
    S.work j = ENNReal.ofReal (((p.stop - p.start) * p.rate j : ℚ) : ℝ) ∧
    S.moment j = ENNReal.ofReal (((p.stop ^ 2 - p.start ^ 2) / 2 * p.rate j : ℚ) : ℝ) := by
  obtain ⟨_, hab, hz0, hz1, _⟩ := hp
  dsimp only
  exact ⟨(Operation.toLabeled_work _ _ j).trans
      (congrArg (fun x : ℚ => ENNReal.ofReal (x : ℝ)) (realizePhase_work hab j (hz0 j) (hz1 j))),
    (Operation.toLabeled_moment _ _ j).trans
      (congrArg (fun x : ℚ => ENNReal.ofReal (x : ℝ))
        (realizePhase_moment hab j (hz0 j) (hz1 j)))⟩

/-- The assignment constructed by reflection is feasible for the supplied
phase workloads in the unrestricted measurable model. -/
theorem realize_measurable_feasible {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) :
    (Operation.toLabeled (realize phases) (realize_valid phases hvalid hjoin)).toActivity.Feasible m
      (fun j => (phases.map fun p => (p.stop - p.start) * p.rate j).sum) :=
  (Operation.toLabeled (realize phases) (realize_valid phases hvalid hjoin)).toActivity_feasible _
    (fun j => (realize_measurable_totals phases hvalid hjoin j).1)

end TBB
