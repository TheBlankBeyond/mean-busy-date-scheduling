import TBB.RealizationKernel
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Chain

namespace TBB

open scoped BigOperators

/-- A half-open rational operation record. The row bound is proved for the
emitted records, so the executable constructor needs no proof input. -/
structure Operation (n : ℕ) where
  start : ℚ
  stop : ℚ
  machine : ℕ
  job : Fin n
  deriving Repr, DecidableEq

def Operation.length {n : ℕ} (op : Operation n) : ℚ := op.stop - op.start

def Operation.moment {n : ℕ} (op : Operation n) : ℚ :=
  (op.stop ^ 2 - op.start ^ 2) / 2

def Operation.Separated {n : ℕ} (op other : Operation n) : Prop :=
  op.stop ≤ other.start ∨ other.stop ≤ op.start

def Operation.Compatible {n : ℕ} (op other : Operation n) : Prop :=
  op.machine = other.machine ∨ op.job = other.job → op.Separated other

def halfWidth (a b : ℚ) : ℚ := (b - a) / 2

/-- Unfiltered candidate obtained by placing a normalized row fragment in the
first half or by reflecting that fragment through the midpoint. -/
def candidate {n : ℕ} (a b : ℚ) (j : Fin n) (x w : ℚ)
    (tail reflected : Bool) : Operation n :=
  let piece := rowFragment x w tail
  let h := halfWidth a b
  if reflected then
    ⟨b - h * piece.last, b - h * piece.first, piece.row.toNat, j⟩
  else
    ⟨a + h * piece.first, a + h * piece.last, piece.row.toNat, j⟩

private theorem candidate_job {n : ℕ} (a b : ℚ) (j : Fin n) (x w : ℚ) (t r : Bool) :
    (candidate a b j x w t r).job = j := by
  cases r <;> rfl

private theorem candidate_machine {n : ℕ} (a b : ℚ) (j : Fin n) (x w : ℚ) (t r : Bool) :
    (candidate a b j x w t r).machine = (rowFragment x w t).row.toNat := by
  cases r <;> rfl

private theorem candidate_length {n : ℕ} (a b : ℚ) (j : Fin n) (x w : ℚ) (t r : Bool) :
    (candidate a b j x w t r).length =
      halfWidth a b * ((rowFragment x w t).last - (rowFragment x w t).first) := by
  cases r <;> simp only [candidate, Bool.false_eq_true, if_false, if_true, Operation.length] <;> ring

private theorem candidate_reflection_moment {n : ℕ} (a b : ℚ) (j : Fin n)
    (x w : ℚ) (t : Bool) :
    (candidate a b j x w t false).moment + (candidate a b j x w t true).moment =
      (a + b) * (candidate a b j x w t false).length := by
  simp only [candidate, Bool.false_eq_true, if_false, if_true, Operation.moment, Operation.length]
  ring

private theorem candidate_bounds {n : ℕ} {a b : ℚ} (hab : a ≤ b) (j : Fin n)
    (x w : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (t r : Bool) :
    a ≤ (candidate a b j x w t r).start ∧
      (candidate a b j x w t r).start ≤ (candidate a b j x w t r).stop ∧
      (candidate a b j x w t r).stop ≤ b := by
  have hp := rowFragment_interval x w hw0 hw1 t
  have hh : 0 ≤ halfWidth a b := by unfold halfWidth; linarith
  have hasa := mul_nonneg hh hp.1
  have horder := mul_le_mul_of_nonneg_left hp.2.1 hh
  have htop := mul_le_mul_of_nonneg_left hp.2.2 hh
  have heq : 2 * halfWidth a b = b - a := by unfold halfWidth; ring
  cases r <;> simp only [candidate, Bool.false_eq_true, if_false, if_true]
  all_goals refine ⟨?_, ?_, ?_⟩ <;> linarith

private theorem candidate_fragment_pos {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {j : Fin n} {x w : ℚ} {t r : Bool}
    (h : (candidate a b j x w t r).start < (candidate a b j x w t r).stop) :
    (rowFragment x w t).first < (rowFragment x w t).last := by
  have hh : 0 ≤ halfWidth a b := by unfold halfWidth; linarith
  by_contra! hbad
  have hprod := mul_le_mul_of_nonneg_left hbad hh
  cases r <;> simp only [candidate, Bool.false_eq_true, if_false, if_true] at h <;> linarith

private theorem candidate_same_half_sep {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {j k : Fin n} {x y w v : ℚ} {t u : Bool} (r : Bool)
    (h : (rowFragment x w t).last ≤ (rowFragment y v u).first) :
    (candidate a b j x w t r).Separated (candidate a b k y v u r) := by
  have hh : 0 ≤ halfWidth a b := by unfold halfWidth; linarith
  have hp := mul_le_mul_of_nonneg_left h hh
  cases r <;> simp only [Operation.Separated, candidate, Bool.false_eq_true, if_false, if_true]
  · left; linarith
  · right; linarith

private theorem candidate_mixed_half_sep {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {j k : Fin n} {x y w v : ℚ} {t u : Bool}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (candidate a b j x w t false).Separated (candidate a b k y v u true) := by
  have hh : 0 ≤ halfWidth a b := by unfold halfWidth; linarith
  have hp := mul_le_mul_of_nonneg_left (rowFragment_interval x w hw0 hw1 t).2.2 hh
  have hq := mul_le_mul_of_nonneg_left (rowFragment_interval y v hv0 hv1 u).2.2 hh
  have heq : 2 * halfWidth a b = b - a := by unfold halfWidth; ring
  simp only [Operation.Separated, candidate, Bool.false_eq_true, if_false, if_true]
  left
  linarith

private theorem Operation.separated_symm {n : ℕ} {op other : Operation n}
    (h : op.Separated other) : other.Separated op := h.elim Or.inr Or.inl

private def slots : List (Bool × Bool) :=
  [(false, false), (true, false), (false, true), (true, true)]

private def jobCandidates {n : ℕ} (a b : ℚ) (z : Fin n → ℚ) (j : Fin n) :
    List (Operation n) :=
  slots.map fun s => candidate a b j (ratePrefix z j.val) (z j) s.1 s.2

private def nonemptyOperation {n : ℕ} (op : Operation n) : Bool :=
  decide (op.start < op.stop)

/-- Reflected operation records for one job and one phase. -/
def realizeJobPhase {n : ℕ} (a b : ℚ) (z : Fin n → ℚ) (j : Fin n) :
    List (Operation n) :=
  (jobCandidates a b z j).filter nonemptyOperation

/-- Executable row wrapping and reflection for one rational phase.
Only positive-length operations are emitted. -/
def realizePhase {n : ℕ} (a b : ℚ) (z : Fin n → ℚ) : List (Operation n) :=
  (List.finRange n).flatMap (realizeJobPhase a b z)

private theorem jobOperations_mem {n : ℕ} {a b : ℚ} {z : Fin n → ℚ}
    {j : Fin n} {op : Operation n} (hop : op ∈ realizeJobPhase a b z j) :
    ∃ t r : Bool, op = candidate a b j (ratePrefix z j.val) (z j) t r ∧ op.start < op.stop := by
  unfold realizeJobPhase jobCandidates at hop
  obtain ⟨hraw, hlen⟩ := List.mem_filter.mp hop
  obtain ⟨s, _, hs⟩ := List.mem_map.mp hraw
  exact ⟨s.1, s.2, hs.symm, of_decide_eq_true hlen⟩

private theorem pairwise_jobOperations {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {z : Fin n → ℚ} (j : Fin n) (hw0 : 0 ≤ z j) (hw1 : z j ≤ 1) :
    (realizeJobPhase a b z j).Pairwise Operation.Compatible := by
  have hs : slots.Pairwise (· ≠ ·) := by decide
  unfold realizeJobPhase jobCandidates
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  refine hs.imp ?_
  intro s u hne _
  rcases s with ⟨t, r⟩
  rcases u with ⟨v, q⟩
  cases r <;> cases q
  · have htv : t ≠ v := by
      intro he
      subst v
      exact hne rfl
    cases t <;> cases v
    · exact (htv rfl).elim
    · exact Operation.separated_symm (candidate_same_half_sep hab false (rowFragment_job_separation _ _ hw1))
    · exact candidate_same_half_sep hab false (rowFragment_job_separation _ _ hw1)
    · exact (htv rfl).elim
  · exact candidate_mixed_half_sep hab hw0 hw1 hw0 hw1
  · exact Operation.separated_symm (candidate_mixed_half_sep hab hw0 hw1 hw0 hw1)
  · have htv : t ≠ v := by
      intro he
      subst v
      exact hne rfl
    cases t <;> cases v
    · exact (htv rfl).elim
    · exact Operation.separated_symm (candidate_same_half_sep hab true (rowFragment_job_separation _ _ hw1))
    · exact candidate_same_half_sep hab true (rowFragment_job_separation _ _ hw1)
    · exact (htv rfl).elim

private theorem separated_distinct_jobs {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {z : Fin n → ℚ} (hz0 : ∀ j, 0 ≤ z j) (hz1 : ∀ j, z j ≤ 1)
    {j k : Fin n} (hjk : j < k) {op other : Operation n}
    (hop : op ∈ realizeJobPhase a b z j) (hother : other ∈ realizeJobPhase a b z k) :
    op.Compatible other := by
  obtain ⟨t, r, rfl, hpos⟩ := jobOperations_mem hop
  obtain ⟨u, s, rfl, hpos'⟩ := jobOperations_mem hother
  intro hc
  rcases hc with hm | hj
  · simp only [candidate_machine] at hm
    have hx := ratePrefix_nonneg hz0 j.val
    have hy := ratePrefix_nonneg hz0 k.val
    have hx' := rowFragment_row_nonneg (w := z j) hx t
    have hy' := rowFragment_row_nonneg (w := z k) hy u
    have hr : (rowFragment (ratePrefix z j.val) (z j) t).row =
        (rowFragment (ratePrefix z k.val) (z k) u).row := by
      rw [← Int.toNat_of_nonneg hx', ← Int.toNat_of_nonneg hy', hm]
    have hstep : j.val + 1 ≤ k.val := by exact hjk
    have horder : ratePrefix z j.val + z j ≤ ratePrefix z k.val := by
      rw [← ratePrefix_succ]
      exact ratePrefix_mono hz0 hstep
    have hnorm := rowFragment_machine_separation horder
      (candidate_fragment_pos hab hpos) (candidate_fragment_pos hab hpos') hr
    cases r <;> cases s
    · exact candidate_same_half_sep hab false hnorm
    · exact candidate_mixed_half_sep hab (hz0 _) (hz1 _) (hz0 _) (hz1 _)
    · exact Operation.separated_symm (candidate_mixed_half_sep hab (hz0 _) (hz1 _) (hz0 _) (hz1 _))
    · exact candidate_same_half_sep hab true hnorm
  · simp only [candidate_job] at hj
    have hlt : j.val < k.val := hjk
    exact (ne_of_lt hlt (congrArg Fin.val hj)).elim

/-- The output has exclusive machines and jobs under the half-open convention. -/
theorem realizePhase_pairwise {n : ℕ} {a b : ℚ} (hab : a ≤ b) {z : Fin n → ℚ}
    (hz0 : ∀ j, 0 ≤ z j) (hz1 : ∀ j, z j ≤ 1) :
    (realizePhase a b z).Pairwise Operation.Compatible := by
  unfold realizePhase
  apply List.pairwise_flatMap.mpr
  refine ⟨fun j _ => pairwise_jobOperations hab j (hz0 j) (hz1 j), ?_⟩
  refine (List.nodup_finRange n).imp ?_
  intro j k hne op hop other hother
  have hval : j.val ≠ k.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact separated_distinct_jobs hab hz0 hz1 hlt hop hother
  · intro hc
    have hswap : other.machine = op.machine ∨ other.job = op.job :=
      hc.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    exact Operation.separated_symm (separated_distinct_jobs hab hz0 hz1 hgt hother hop hswap)

/-- Each emitted record is nonempty, remains in its input phase and uses a
valid row. When the phase has equal endpoints no record can be emitted. -/
theorem realizePhase_operation {n m : ℕ} {a b : ℚ} (hab : a ≤ b) {z : Fin n → ℚ}
    (hz0 : ∀ j, 0 ≤ z j) (hz1 : ∀ j, z j ≤ 1) (hcap : ∑ j, z j ≤ (m : ℚ))
    {op : Operation n} (hop : op ∈ realizePhase a b z) :
    a ≤ op.start ∧ op.start < op.stop ∧ op.stop ≤ b ∧ op.machine < m := by
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hop
  obtain ⟨t, r, rfl, hpos⟩ := jobOperations_mem hj
  have hb := candidate_bounds hab j (ratePrefix z j.val) (z j) (hz0 j) (hz1 j) t r
  refine ⟨hb.1, hpos, hb.2.2, ?_⟩
  have hm : ratePrefix z j.val + z j ≤ (m : ℚ) := by
    rw [← ratePrefix_succ]
    exact (ratePrefix_mono hz0 j.isLt).trans (ratePrefix_end z ▸ hcap)
  rw [candidate_machine]
  exact rowFragment_machine_bound (ratePrefix_nonneg hz0 _) (hz0 _) (hz1 _) hm
    (candidate_fragment_pos hab hpos)


/-- Sum a rational quantity over all operations of a job. -/
def operationTally {n : ℕ} (quantity : Operation n → ℚ) (job : Fin n)
    (ops : List (Operation n)) : ℚ :=
  (ops.map fun op => if op.job = job then quantity op else 0).sum

def operationWork {n : ℕ} (ops : List (Operation n)) (job : Fin n) : ℚ :=
  operationTally Operation.length job ops

def operationMoment {n : ℕ} (ops : List (Operation n)) (job : Fin n) : ℚ :=
  operationTally Operation.moment job ops

private theorem sumMapFlatMap {α β : Type} (l : List α) (f : α → List β) (g : β → ℚ) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

private theorem sumMapFilter {α : Type} (l : List α) (g : α → ℚ) (p : α → Bool)
    (hz : ∀ x ∈ l, p x = false → g x = 0) :
    ((l.filter p).map g).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have htail : ∀ y ∈ l, p y = false → g y = 0 :=
      fun y hy => hz y (List.mem_cons_of_mem _ hy)
    cases h : p x
    · have hzero := hz x (List.mem_cons_self ..) h
      simp [h, hzero, ih htail]
    · simp [h, ih htail]

private theorem tally_realizePhase {n : ℕ} (a b : ℚ) (z : Fin n → ℚ) (j : Fin n)
    (g : Operation n → ℚ) :
    operationTally g j (realizePhase a b z) = ((realizeJobPhase a b z j).map g).sum := by
  let f (k : Fin n) := operationTally g j (realizeJobPhase a b z k)
  have hsingle : ∀ k, k ≠ j → k ∈ List.finRange n → f k = 0 := by
    intro k hkj _
    unfold f operationTally
    rw [List.map_congr_left (g := fun _ => (0 : ℚ)) (by
      intro op hop
      obtain ⟨t, r, rfl, _⟩ := jobOperations_mem hop
      simp [candidate_job, hkj])]
    simp
  change (((List.finRange n).flatMap (realizeJobPhase a b z)).map fun op =>
    if op.job = j then g op else 0).sum = _
  rw [sumMapFlatMap]
  change ((List.finRange n).map f).sum = _
  rw [List.sum_map_eq_nsmul_single j f hsingle]
  rw [List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange j), one_nsmul]
  unfold f operationTally
  rw [List.map_congr_left (g := g) (by
    intro op hop
    obtain ⟨t, r, rfl, _⟩ := jobOperations_mem hop
    simp [candidate_job])]

private theorem sumJobCandidates {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {z : Fin n → ℚ} (j : Fin n) (hz0 : 0 ≤ z j) (hz1 : z j ≤ 1)
    (g : Operation n → ℚ) (hg : ∀ op, op.start = op.stop → g op = 0) :
    ((realizeJobPhase a b z j).map g).sum = ((jobCandidates a b z j).map g).sum := by
  unfold realizeJobPhase
  apply sumMapFilter
  intro op hop hzero
  unfold jobCandidates at hop
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hop
  have hbound := candidate_bounds hab j (ratePrefix z j.val) (z j) hz0 hz1 s.1 s.2
  have hn : ¬ (candidate a b j (ratePrefix z j.val) (z j) s.1 s.2).start <
      (candidate a b j (ratePrefix z j.val) (z j) s.1 s.2).stop := by
    simpa [nonemptyOperation] using hzero
  exact hg _ (le_antisymm hbound.2.1 (le_of_not_gt hn))

private theorem forward_length_sum {n : ℕ} (a b : ℚ) (j : Fin n) (x w : ℚ) :
    (candidate a b j x w false false).length +
      (candidate a b j x w true false).length = halfWidth a b * w := by
  rw [candidate_length, candidate_length, ← mul_add, rowFragment_total]

/-- Phase workload is preserved exactly as a rational number for each job. -/
theorem realizePhase_work {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {z : Fin n → ℚ} (j : Fin n) (hz0 : 0 ≤ z j) (hz1 : z j ≤ 1) :
    operationWork (realizePhase a b z) j = (b - a) * z j := by
  unfold operationWork
  rw [tally_realizePhase, sumJobCandidates hab j hz0 hz1 _ (by
    intro op h; simp [Operation.length, h])]
  simp only [jobCandidates, slots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  let x := ratePrefix z j.val
  let w := z j
  have hsame (t : Bool) :
      (candidate a b j x w t true).length = (candidate a b j x w t false).length := by
    simp only [candidate_length]
  change (candidate a b j x w false false).length +
    ((candidate a b j x w true false).length +
    ((candidate a b j x w false true).length +
     (candidate a b j x w true true).length)) = (b - a) * w
  rw [hsame false, hsame true]
  calc
    _ = 2 * ((candidate a b j x w false false).length +
        (candidate a b j x w true false).length) := by ring
    _ = _ := by rw [forward_length_sum]; unfold halfWidth; ring

/-- Every individual first moment is preserved exactly. Reflection pairs make
the moment equal the midpoint time multiplied by the full workload. -/
theorem realizePhase_moment {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {z : Fin n → ℚ} (j : Fin n) (hz0 : 0 ≤ z j) (hz1 : z j ≤ 1) :
    operationMoment (realizePhase a b z) j = (b ^ 2 - a ^ 2) / 2 * z j := by
  unfold operationMoment
  rw [tally_realizePhase, sumJobCandidates hab j hz0 hz1 _ (by
    intro op h; simp [Operation.moment, h])]
  simp only [jobCandidates, slots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  let x := ratePrefix z j.val
  let w := z j
  change (candidate a b j x w false false).moment +
    ((candidate a b j x w true false).moment +
    ((candidate a b j x w false true).moment +
     (candidate a b j x w true true).moment)) = (b ^ 2 - a ^ 2) / 2 * w
  calc
    _ = ((candidate a b j x w false false).moment + (candidate a b j x w false true).moment) +
        ((candidate a b j x w true false).moment + (candidate a b j x w true true).moment) := by ring
    _ = (a + b) * ((candidate a b j x w false false).length +
        (candidate a b j x w true false).length) := by
      rw [candidate_reflection_moment, candidate_reflection_moment]
      ring
    _ = _ := by rw [forward_length_sum]; unfold halfWidth; ring

/-- At most two positive records for a job lie in the first half. -/
theorem realizeJobPhase_firstHalf_count {n : ℕ} {a b : ℚ} (hab : a ≤ b)
    {z : Fin n → ℚ} (j : Fin n) (hz0 : 0 ≤ z j) (hz1 : z j ≤ 1) :
    ((realizeJobPhase a b z j).filter
      (fun op => decide (op.stop ≤ a + halfWidth a b))).length ≤ 2 := by
  unfold realizeJobPhase
  rw [List.filter_filter]
  let keep (op : Operation n) : Bool := decide (op.stop ≤ a + halfWidth a b) &&
    nonemptyOperation op
  let x := ratePrefix z j.val
  let w := z j
  have hh : 0 ≤ halfWidth a b := by unfold halfWidth; linarith
  have heq : 2 * halfWidth a b = b - a := by unfold halfWidth; ring
  have hskip (t : Bool) : keep (candidate a b j x w t true) = false := by
    have htop := mul_le_mul_of_nonneg_left (rowFragment_interval x w hz0 hz1 t).2.2 hh
    have hstart : a + halfWidth a b ≤ (candidate a b j x w t true).start := by
      simp only [candidate, if_true]
      linarith
    by_cases hp : (candidate a b j x w t true).start < (candidate a b j x w t true).stop
    · have hn : ¬ (candidate a b j x w t true).stop ≤ a + halfWidth a b := by linarith
      simp [keep, hn]
    · simp [keep, nonemptyOperation, hp]
  change ([candidate a b j x w false false, candidate a b j x w true false,
      candidate a b j x w false true, candidate a b j x w true true].filter keep).length ≤ 2
  cases hf : keep (candidate a b j x w false false) <;>
    cases ht : keep (candidate a b j x w true false) <;> simp [hf, ht, hskip]

/-- If machine supply exceeds the number of jobs, no extra row is needed. -/
theorem realizePhase_machine_min {n m : ℕ} {a b : ℚ} (hab : a ≤ b) {z : Fin n → ℚ}
    (hz0 : ∀ j, 0 ≤ z j) (hz1 : ∀ j, z j ≤ 1) (hcap : ∑ j, z j ≤ (m : ℚ))
    {op : Operation n} (hop : op ∈ realizePhase a b z) :
    op.machine < min m n := by
  have hn : ∑ j, z j ≤ (n : ℚ) := calc
    _ ≤ ∑ _ : Fin n, (1 : ℚ) := Finset.sum_le_sum fun j _ => hz1 j
    _ = _ := by simp
  exact lt_min (realizePhase_operation hab hz0 hz1 hcap hop).2.2.2
    (realizePhase_operation hab hz0 hz1 hn hop).2.2.2

theorem realizePhase_equal_endpoints {n : ℕ} (a : ℚ) (z : Fin n → ℚ) :
    realizePhase a a z = [] := by
  simp [realizePhase, realizeJobPhase, jobCandidates, slots, candidate, halfWidth,
    nonemptyOperation]

/-- A job with rate zero emits no records. -/
theorem realizeJobPhase_zero_rate {n : ℕ} (a b : ℚ) (z : Fin n → ℚ) (j : Fin n)
    (hz : z j = 0) : realizeJobPhase a b z j = [] := by
  have h1 := le_of_lt (rowOffset_lt_one (ratePrefix z j.val))
  have htail : rowOffset (ratePrefix z j.val) - 1 ≤ 0 := sub_nonpos.mpr h1
  simp [realizeJobPhase, jobCandidates, slots, candidate, rowFragment, nonemptyOperation,
    hz, min_eq_right h1, max_eq_left htail]

private theorem flatMap_length_le {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ k) : (l.flatMap f).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

theorem realizePhase_count {n : ℕ} (a b : ℚ) (z : Fin n → ℚ) :
    (realizePhase a b z).length ≤ 4 * n := by
  have hj : ∀ j ∈ List.finRange n, (realizeJobPhase a b z j).length ≤ 4 := by
    intro j _
    calc
      _ ≤ (jobCandidates a b z j).length := List.length_filter_le _ _
      _ = 4 := by simp [jobCandidates, slots]
  simpa only [realizePhase, List.length_finRange] using
    flatMap_length_le (List.finRange n) (realizeJobPhase a b z) 4 hj

/-- Rates stipulated for one time phase of Theorem R. -/
structure AllocationPhase (n : ℕ) where
  start : ℚ
  stop : ℚ
  rate : Fin n → ℚ

/-- The hypotheses of reflected realization on a freely shifted time interval. -/
def AllocationPhase.ValidOnLine {n : ℕ} (m : ℕ) (p : AllocationPhase n) : Prop :=
  p.start ≤ p.stop ∧
    (∀ j, 0 ≤ p.rate j) ∧ (∀ j, p.rate j ≤ 1) ∧ ∑ j, p.rate j ≤ (m : ℚ)

/-- The extra start bound for an input phase of a half-line scheduling instance. -/
def AllocationPhase.Valid {n : ℕ} (m : ℕ) (p : AllocationPhase n) : Prop :=
  0 ≤ p.start ∧ p.ValidOnLine m

def AllocationPhase.operations {n : ℕ} (p : AllocationPhase n) : List (Operation n) :=
  realizePhase p.start p.stop p.rate

/-- The executable construction for a list of consecutive phases. -/
def realize {n : ℕ} (phases : List (AllocationPhase n)) : List (Operation n) :=
  phases.flatMap AllocationPhase.operations

private theorem consecutive_pairwise {n : ℕ} (phases : List (AllocationPhase n))
    (hlength : ∀ p ∈ phases, p.start ≤ p.stop)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) :
    phases.Pairwise (fun p q => p.stop ≤ q.start) := by
  induction phases with
  | nil => simp
  | cons p phases ih =>
    cases phases with
    | nil => simp
    | cons q qs =>
      have he : p.stop = q.start := (List.isChain_cons_cons.mp hjoin).1
      have htail := ih (fun ph hp => hlength ph (List.mem_cons_of_mem p hp))
        (List.isChain_cons_cons.mp hjoin).2
      apply List.pairwise_cons.mpr
      refine ⟨?_, htail⟩
      intro v hv
      rcases List.mem_cons.mp hv with eq | hmem
      · subst v
        exact he.le
      · exact he.le.trans ((hlength q (by simp)).trans ((List.pairwise_cons.mp htail).1 v hmem))

theorem realize_pairwise_on_line {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.ValidOnLine m)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) :
    (realize phases).Pairwise Operation.Compatible := by
  unfold realize
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p hp
    obtain ⟨hab, hz0, hz1, _⟩ := hvalid p hp
    exact realizePhase_pairwise hab hz0 hz1
  · refine (consecutive_pairwise phases (fun p hp => (hvalid p hp).1) hjoin).imp_of_mem ?_
    intro p q hp hq hpq op hop other hother _
    obtain ⟨hab, hz0, hz1, hcap⟩ := hvalid p hp
    obtain ⟨hab', hz0', hz1', hcap'⟩ := hvalid q hq
    exact Or.inl ((realizePhase_operation hab hz0 hz1 hcap hop).2.2.1.trans
      (hpq.trans (realizePhase_operation hab' hz0' hz1' hcap' hother).1))

theorem realize_pairwise {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) :
    (realize phases).Pairwise Operation.Compatible :=
  realize_pairwise_on_line phases (fun p hp => (hvalid p hp).2) hjoin

theorem realize_operation_on_line {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.ValidOnLine m) {op : Operation n} (hop : op ∈ realize phases) :
    ∃ p ∈ phases, p.start ≤ op.start ∧ op.start < op.stop ∧ op.stop ≤ p.stop ∧ op.machine < m := by
  obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp hop
  obtain ⟨hab, hz0, hz1, hcap⟩ := hvalid p hp
  exact ⟨p, hp, realizePhase_operation hab hz0 hz1 hcap h⟩

theorem realize_operation {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m) {op : Operation n} (hop : op ∈ realize phases) :
    0 ≤ op.start ∧ op.start < op.stop ∧ op.machine < m := by
  obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp hop
  obtain ⟨h0, hab, hz0, hz1, hcap⟩ := hvalid p hp
  obtain ⟨hstart, hpos, _, hm⟩ := realizePhase_operation hab hz0 hz1 hcap h
  exact ⟨h0.trans hstart, hpos, hm⟩

theorem realize_count {n : ℕ} (phases : List (AllocationPhase n)) :
    (realize phases).length ≤ 4 * n * phases.length :=
  flatMap_length_le phases AllocationPhase.operations (4 * n)
    (fun p _ => realizePhase_count p.start p.stop p.rate)

/-- The full shifted-interval form of Theorem R. The time coordinates may be
any rationals. The construction is still the same executable row wrapping and
reflection, for any finite consecutive sequence of phases. -/
theorem reflected_realization_on_line {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.ValidOnLine m)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) :
    (realize phases).Pairwise Operation.Compatible ∧
      (∀ op ∈ realize phases, ∃ p ∈ phases,
        p.start ≤ op.start ∧ op.start < op.stop ∧ op.stop ≤ p.stop ∧ op.machine < m) ∧
      (∀ p ∈ phases, ∀ j,
        operationWork p.operations j = (p.stop - p.start) * p.rate j ∧
        operationMoment p.operations j = (p.stop ^ 2 - p.start ^ 2) / 2 * p.rate j) ∧
      (realize phases).length ≤ 4 * n * phases.length := by
  refine ⟨realize_pairwise_on_line phases hvalid hjoin,
    fun _ hop => realize_operation_on_line phases hvalid hop, ?_, realize_count phases⟩
  intro p hp j
  obtain ⟨hab, hz0, hz1, _⟩ := hvalid p hp
  exact ⟨realizePhase_work hab j (hz0 j) (hz1 j), realizePhase_moment hab j (hz0 j) (hz1 j)⟩

/-- Theorem R. Each phase contributes exactly its stipulated workload and first
moment, and concatenation produces one nonoverlapping list of valid operations. -/
theorem reflected_realization {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m)
    (hjoin : phases.IsChain (fun p q => p.stop = q.start)) :
    (realize phases).Pairwise Operation.Compatible ∧
      (∀ op ∈ realize phases, 0 ≤ op.start ∧ op.start < op.stop ∧ op.machine < m) ∧
      (∀ p ∈ phases, ∀ j,
        operationWork p.operations j = (p.stop - p.start) * p.rate j ∧
        operationMoment p.operations j = (p.stop ^ 2 - p.start ^ 2) / 2 * p.rate j) ∧
      (realize phases).length ≤ 4 * n * phases.length := by
  refine ⟨realize_pairwise phases hvalid hjoin, fun _ hop => realize_operation phases hvalid hop, ?_,
    realize_count phases⟩
  intro p hp j
  obtain ⟨_, hab, hz0, hz1, _⟩ := hvalid p hp
  exact ⟨realizePhase_work hab j (hz0 j) (hz1 j), realizePhase_moment hab j (hz0 j) (hz1 j)⟩

/-- Restricting the concatenated output to a phase recovers exactly its own
operation list. Strictly positive record lengths remove ambiguity at shared
endpoints, including runs of zero-length phases. -/
theorem realize_restrict_phase_on_line {n m : ℕ}
    (before after : List (AllocationPhase n)) (p : AllocationPhase n)
    (hvalid : ∀ ph ∈ before ++ p :: after, ph.ValidOnLine m)
    (hjoin : (before ++ p :: after).IsChain (fun ph q => ph.stop = q.start)) :
    ((realize (before ++ p :: after)).filter
      (fun op => decide (p.start ≤ op.start ∧ op.stop ≤ p.stop))) =
      p.operations := by
  let inside (op : Operation n) := decide (p.start ≤ op.start ∧ op.stop ≤ p.stop)
  have hord := List.pairwise_append.mp (consecutive_pairwise (before ++ p :: after)
    (fun ph hph => (hvalid ph hph).1) hjoin)
  have hbefore : (realize before).filter inside = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro op hop hinside
    obtain ⟨ph, hph, hop'⟩ := List.mem_flatMap.mp hop
    obtain ⟨hb, hz0, hz1, hc⟩ := hvalid ph (by simp [hph])
    have hstop := realizePhase_operation hb hz0 hz1 hc hop'
    have hsep := hord.2.2 ph hph p (by simp)
    have hints : p.start ≤ op.start ∧ op.stop ≤ p.stop := of_decide_eq_true hinside
    linarith [hstop.2.1, hstop.2.2.1, hints.1]
  have hafter : (realize after).filter inside = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro op hop hinside
    obtain ⟨ph, hph, hop'⟩ := List.mem_flatMap.mp hop
    obtain ⟨hb, hz0, hz1, hc⟩ := hvalid ph (by simp [hph])
    have hstart := realizePhase_operation hb hz0 hz1 hc hop'
    have hsep := (List.pairwise_cons.mp hord.2.1).1 ph hph
    have hints : p.start ≤ op.start ∧ op.stop ≤ p.stop := of_decide_eq_true hinside
    linarith [hstart.1, hstart.2.1, hints.2]
  have hp : p.operations.filter inside = p.operations := by
    apply List.filter_eq_self.mpr
    intro op hop
    obtain ⟨hb, hz0, hz1, hc⟩ := hvalid p (by simp)
    have ho := realizePhase_operation hb hz0 hz1 hc hop
    exact decide_eq_true ⟨ho.1, ho.2.2.1⟩
  change (realize (before ++ p :: after)).filter inside = _
  simp only [realize, List.flatMap_append, List.flatMap_cons, List.filter_append] at hbefore hafter ⊢
  simp [hbefore, hp, hafter]

theorem realize_restrict_phase {n m : ℕ}
    (before after : List (AllocationPhase n)) (p : AllocationPhase n)
    (hvalid : ∀ ph ∈ before ++ p :: after, ph.Valid m)
    (hjoin : (before ++ p :: after).IsChain (fun ph q => ph.stop = q.start)) :
    ((realize (before ++ p :: after)).filter
      (fun op => decide (p.start ≤ op.start ∧ op.stop ≤ p.stop))) =
      p.operations :=
  realize_restrict_phase_on_line before after p (fun ph hp => (hvalid ph hp).2) hjoin

/-- The exact total workload is the sum of the phase workloads. -/
theorem realize_total_work {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m) (j : Fin n) :
    operationWork (realize phases) j = (phases.map fun p => (p.stop - p.start) * p.rate j).sum := by
  unfold operationWork operationTally realize
  rw [sumMapFlatMap]
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨_, hab, hz0, hz1, _⟩ := hvalid p hp
  exact realizePhase_work hab j (hz0 j) (hz1 j)

/-- The exact total first moment is the sum of the individual phase moments. -/
theorem realize_total_moment {n m : ℕ} (phases : List (AllocationPhase n))
    (hvalid : ∀ p ∈ phases, p.Valid m) (j : Fin n) :
    operationMoment (realize phases) j =
      (phases.map fun p => (p.stop ^ 2 - p.start ^ 2) / 2 * p.rate j).sum := by
  unfold operationMoment operationTally realize
  rw [sumMapFlatMap]
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨_, hab, hz0, hz1, _⟩ := hvalid p hp
  exact realizePhase_moment hab j (hz0 j) (hz1 j)

end TBB
