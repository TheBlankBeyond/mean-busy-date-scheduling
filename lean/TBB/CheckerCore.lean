import TBB.Finite
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

namespace TBB

open scoped BigOperators

/-- The portable, untrusted input format. Indices are zero-based. -/
structure RawPhase where
  start : ℚ
  stop : ℚ
  assigned : List (ℕ × ℕ)
  startThreshold : ℚ
  stopThreshold : ℚ
  deriving Repr

/-- The proposed data, including claimed per-job moments and exact objective. -/
structure RawCertificate where
  n : ℕ
  m : ℕ
  work : List ℚ
  alpha : List ℚ
  multiplier : List ℚ
  individualMoments : List ℚ
  horizon : ℚ
  objective : ℚ
  schedule : List RawPhase
  deriving Repr

/-- The thresholds witness endpoint upper bounds for one phase. -/
structure CertifiedPhase (n m : ℕ) where
  phase : Phase n m
  startThreshold : ℚ
  stopThreshold : ℚ

/-- Dimension-checked certificate data. A decoded certificate still needs validation. -/
structure Certificate (n m : ℕ) where
  work : Fin n → ℚ
  alpha : Fin n → ℚ
  multiplier : Fin n → ℚ
  individualMoments : Fin n → ℚ
  horizon : ℚ
  objective : ℚ
  entries : List (CertifiedPhase n m)

def Certificate.schedule (c : Certificate n m) : Schedule n m :=
  c.entries.map CertifiedPhase.phase

private def decodeAssignment (n m : ℕ) (a : ℕ × ℕ) : Option (Fin m × Fin n) :=
  if hm : a.1 < m then
    if hn : a.2 < n then some (⟨a.1, hm⟩, ⟨a.2, hn⟩) else none
  else none

private def decodePhase (n m : ℕ) (I : RawPhase) : Option (CertifiedPhase n m) := do
  let assigned ← I.assigned.mapM (decodeAssignment n m)
  return ⟨⟨I.start, I.stop, assigned⟩, I.startThreshold, I.stopThreshold⟩

/-- Decode only when every vector has the declared dimension and indices are in range. -/
def RawCertificate.decode (c : RawCertificate) : Option (Certificate c.n c.m) :=
  if dimensions : c.work.length = c.n ∧ c.alpha.length = c.n ∧
      c.multiplier.length = c.n ∧ c.individualMoments.length = c.n then do
    let entries ← c.schedule.mapM (decodePhase c.n c.m)
    return {
      work := fun j => c.work[j.val]'(by simpa only [dimensions.1] using j.isLt)
      alpha := fun j => c.alpha[j.val]'(by simpa only [dimensions.2.1] using j.isLt)
      multiplier := fun j => c.multiplier[j.val]'(by simpa only [dimensions.2.2.1] using j.isLt)
      individualMoments := fun j => c.individualMoments[j.val]'(by simpa only [dimensions.2.2.2] using j.isLt)
      horizon := c.horizon
      objective := c.objective
      entries := entries }
  else none

theorem RawCertificate.decode_objective {raw : RawCertificate} {c : Certificate raw.n raw.m}
    (h : raw.decode = some c) : c.objective = raw.objective := by
  unfold RawCertificate.decode at h
  split at h
  next _ =>
    cases hd : raw.schedule.mapM (decodePhase raw.n raw.m) <;> simp [hd] at h
    subst c
    rfl
  next _ =>
    simp at h

/-- A partition of an interval by nonempty half-open phases, including idle phases. -/
def CoversFrom (start : ℚ) (S : Schedule n m) (stop : ℚ) : Prop :=
  match S with
  | [] => start = stop
  | I :: tail => start = I.start ∧ I.start < I.stop ∧ CoversFrom I.stop tail stop

instance (start : ℚ) (S : Schedule n m) (stop : ℚ) :
    Decidable (CoversFrom start S stop) := by
  induction S generalizing start with
  | nil =>
    change Decidable (start = stop)
    infer_instance
  | cons I S ih =>
    letI := ih I.stop
    change Decidable (start = I.start ∧ I.start < I.stop ∧ CoversFrom I.stop S stop)
    infer_instance

theorem CoversFrom.bounds {S : Schedule n m} {a b : ℚ} (h : CoversFrom a S b) :
    a ≤ b ∧ ∀ I ∈ S, a ≤ I.start ∧ I.start < I.stop ∧ I.stop ≤ b := by
  induction S generalizing a with
  | nil =>
    change a = b at h
    simp [h]
  | cons I S ih =>
    change a = I.start ∧ I.start < I.stop ∧ CoversFrom I.stop S b at h
    rcases h with ⟨ha, hp, htail⟩
    rcases ih htail with ⟨hb, hmem⟩
    refine ⟨le_trans (ha.le.trans hp.le) hb, ?_⟩
    intro J hj
    simp only [List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨ha.le, hp, hb⟩
    · obtain ⟨hl, hs, hr⟩ := hmem J hj
      exact ⟨le_trans (ha.le.trans hp.le) hl, hs, hr⟩

theorem CoversFrom.ordered {S : Schedule n m} {a b : ℚ} (h : CoversFrom a S b) :
    S.Pairwise (fun I J => I.stop ≤ J.start) := by
  induction S generalizing a with
  | nil => exact List.Pairwise.nil
  | cons I S ih =>
    change a = I.start ∧ I.start < I.stop ∧ CoversFrom I.stop S b at h
    rw [List.pairwise_cons]
    exact ⟨fun J hJ => (h.2.2.bounds.2 J hJ).1, ih h.2.2⟩

def rationalScore (α lam : Fin n → ℚ) (t : ℚ) (j : Fin n) : ℚ :=
  lam j - t * α j

def rationalThreshold (m : ℕ) (scores : Fin n → ℚ) (threshold : ℚ) : ℚ :=
  (m : ℚ) * threshold + ∑ j, max (scores j - threshold) 0

/-- Score of the phase's job indicator, independently of machine labels. -/
def Phase.rationalScoreValue (I : Phase n m) (scores : Fin n → ℚ) : ℚ :=
  ∑ j, scores j * (if I.active j then 1 else 0)

/-- The endpoint price must be nonnegative and tight for the assigned jobs. -/
def endpointPass (c : Certificate n m) (I : Phase n m) (t threshold : ℚ) : Prop :=
  0 ≤ threshold ∧ I.rationalScoreValue (rationalScore c.alpha c.multiplier t) =
    rationalThreshold m (rationalScore c.alpha c.multiplier t) threshold

instance (c : Certificate n m) (I : Phase n m) (t threshold : ℚ) :
    Decidable (endpointPass c I t threshold) := by
  unfold endpointPass
  infer_instance

def phasePass (c : Certificate n m) (entry : CertifiedPhase n m) : Prop :=
  (entry.phase.assigned.map Prod.fst).Nodup ∧
  (entry.phase.assigned.map Prod.snd).Nodup ∧
  endpointPass c entry.phase entry.phase.start entry.startThreshold ∧
  endpointPass c entry.phase entry.phase.stop entry.stopThreshold

instance (c : Certificate n m) (entry : CertifiedPhase n m) : Decidable (phasePass c entry) := by
  unfold phasePass
  infer_instance

/-- Score integral over the certificate partition. Endpoint tightness is checked separately. -/
def Certificate.scoreIntegral (c : Certificate n m) : ℚ :=
  (c.schedule.map fun I =>
    ∑ j, (c.multiplier j * I.work j - c.alpha j * I.moment j)).sum

/-- The strong, finite checks include the workload, all individual moments, and the dual value. -/
def Certificate.Passes (c : Certificate n m) : Prop :=
  0 < n ∧ 0 < m ∧ 0 ≤ c.horizon ∧
  CoversFrom 0 c.schedule c.horizon ∧
  c.entries.all (fun entry => decide (phasePass c entry)) = true ∧
  (∀ j, 0 < c.work j ∧ 0 < c.alpha j ∧
    c.schedule.work j = c.work j ∧
    c.schedule.moment j = c.individualMoments j ∧
    rationalScore c.alpha c.multiplier c.horizon j ≤ 0) ∧
  c.schedule.cost c.alpha = c.objective ∧
  (∑ j, c.multiplier j * c.work j) - c.scoreIntegral = c.objective

instance (c : Certificate n m) : Decidable c.Passes := by
  unfold Certificate.Passes
  infer_instance

/-- Exact, executable rational checker. Malformed dimensions and indices are rejected. -/
def check (raw : RawCertificate) : Bool :=
  match raw.decode with
  | none => false
  | some c => decide c.Passes

theorem check_iff (raw : RawCertificate) :
    check raw = true ↔ ∃ c, raw.decode = some c ∧ c.Passes := by
  cases h : raw.decode <;> simp [check, h]

theorem Certificate.Passes.valid {c : Certificate n m} (h : c.Passes) :
    c.schedule.ValidAt c.horizon := by
  rcases h with ⟨_, _, _, hp, hentries, _, _, _⟩
  refine ⟨hp.ordered, ?_, ?_, ?_⟩
  · intro I hI
    exact hp.bounds.2 I hI
  · intro I hI
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
    have hp' : phasePass c entry := of_decide_eq_true (List.all_eq_true.mp hentries entry he)
    exact hp'.1
  · intro I hI
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
    have hp' : phasePass c entry := of_decide_eq_true (List.all_eq_true.mp hentries entry he)
    exact hp'.2.1

theorem Certificate.Passes.endpoint_witnesses {c : Certificate n m} (h : c.Passes)
    {I : Phase n m} (hI : I ∈ c.schedule) :
    ∃ left right : ℚ, endpointPass c I I.start left ∧ endpointPass c I I.stop right := by
  rcases h with ⟨_, _, _, _, hentries, _, _, _⟩
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
  have hp' : phasePass c entry := of_decide_eq_true (List.all_eq_true.mp hentries entry he)
  exact ⟨entry.startThreshold, entry.stopThreshold, hp'.2.2⟩

end TBB
