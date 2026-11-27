import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace TBB

open scoped BigOperators

/-- The total rate assigned to jobs strictly preceding index k. -/
def ratePrefix {n : ℕ} (z : Fin n → ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), z j

theorem ratePrefix_mono {n : ℕ} {z : Fin n → ℚ}
    (hz : ∀ j, 0 ≤ z j) {k l : ℕ} (hkl : k ≤ l) :
    ratePrefix z k ≤ ratePrefix z l := by
  unfold ratePrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_lt_of_le hj hkl
  · intro j _ _
    exact hz j

theorem ratePrefix_nonneg {n : ℕ} {z : Fin n → ℚ}
    (hz : ∀ j, 0 ≤ z j) (k : ℕ) : 0 ≤ ratePrefix z k := by
  unfold ratePrefix
  exact Finset.sum_nonneg fun j _ => hz j

theorem ratePrefix_succ {n : ℕ} (z : Fin n → ℚ) (j : Fin n) :
    ratePrefix z (j.val + 1) = ratePrefix z j.val + z j := by
  classical
  let s := Finset.univ.filter (fun k : Fin n => k.val < j.val)
  have hj : j ∉ s := by simp [s]
  have hs : Finset.univ.filter (fun k : Fin n => k.val < j.val + 1) = insert j s := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, s]
    constructor
    · intro h
      by_cases hlt : k.val < j.val
      · exact Or.inr hlt
      · exact Or.inl (Fin.ext (by omega))
    · rintro (h | h)
      · simp [h]
      · omega
  unfold ratePrefix
  rw [hs, Finset.sum_insert hj, add_comm]

theorem ratePrefix_end {n : ℕ} (z : Fin n → ℚ) :
    ratePrefix z n = ∑ j, z j := by
  unfold ratePrefix
  congr 1
  ext j
  simp [j.isLt]

/-- A first-half row fragment in units of half an interval. Zero-length fragments
may occur in this temporary representation and are never emitted. -/
structure RowFragment where
  row : ℤ
  first : ℚ
  last : ℚ
  deriving Repr, DecidableEq

def rowOffset (x : ℚ) : ℚ := x - (⌊x⌋ : ℤ)

def rowFragment (x w : ℚ) (tail : Bool) : RowFragment :=
  if tail then
    ⟨⌊x⌋ + 1, 0, max 0 (rowOffset x + w - 1)⟩
  else
    ⟨⌊x⌋, rowOffset x, min 1 (rowOffset x + w)⟩

theorem rowOffset_nonneg (x : ℚ) : 0 ≤ rowOffset x := by
  exact sub_nonneg.mpr (Int.floor_le x)

theorem rowOffset_lt_one (x : ℚ) : rowOffset x < 1 := by
  have h := Int.lt_floor_add_one x
  change x - (⌊x⌋ : ℚ) < 1
  linarith

theorem rowFragment_interval (x w : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (tail : Bool) :
    0 ≤ (rowFragment x w tail).first ∧
    (rowFragment x w tail).first ≤ (rowFragment x w tail).last ∧
    (rowFragment x w tail).last ≤ 1 := by
  have h0 := rowOffset_nonneg x
  have h1 := rowOffset_lt_one x
  cases tail
  · simp only [rowFragment, Bool.false_eq_true, if_false]
    refine ⟨h0, le_min (le_of_lt h1) ?_, min_le_left _ _⟩
    linarith
  · simp only [rowFragment, if_true]
    refine ⟨le_rfl, le_max_left _ _, max_le (by norm_num) ?_⟩
    linarith

theorem rowFragment_job_separation (x w : ℚ) (hw : w ≤ 1) :
    (rowFragment x w true).last ≤ (rowFragment x w false).first := by
  simp only [rowFragment, if_true, Bool.false_eq_true, if_false]
  exact max_le (rowOffset_nonneg x) (by linarith)

theorem rowFragment_total (x w : ℚ) :
    ((rowFragment x w false).last - (rowFragment x w false).first) +
      ((rowFragment x w true).last - (rowFragment x w true).first) = w := by
  simp only [rowFragment, if_true, Bool.false_eq_true, if_false]
  by_cases h : rowOffset x + w ≤ 1
  · rw [min_eq_right h, max_eq_left (by linarith : rowOffset x + w - 1 ≤ 0)]
    ring
  · have h' : 1 ≤ rowOffset x + w := le_of_lt (lt_of_not_ge h)
    rw [min_eq_left h', max_eq_right (by linarith : 0 ≤ rowOffset x + w - 1)]
    ring

theorem rowFragment_row_nonneg {x w : ℚ} (hx : 0 ≤ x) (tail : Bool) :
    0 ≤ (rowFragment x w tail).row := by
  have hfloor : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  cases tail
  · simpa [rowFragment] using hfloor
  · simp only [rowFragment, if_true]
    omega

/-- The normalized row segment actually lies inside the original cumulative
job block once its row number is added to both endpoints. -/
theorem rowFragment_contained {x w : ℚ} {tail : Bool}
    (hpos : (rowFragment x w tail).first < (rowFragment x w tail).last) :
    x ≤ ((rowFragment x w tail).row : ℚ) + (rowFragment x w tail).first ∧
      ((rowFragment x w tail).row : ℚ) + (rowFragment x w tail).last ≤ x + w := by
  have hx : (⌊x⌋ : ℚ) + rowOffset x = x := by
    change (⌊x⌋ : ℚ) + (x - (⌊x⌋ : ℚ)) = x
    ring
  cases tail
  · simp only [rowFragment, Bool.false_eq_true, if_false]
    constructor
    · rw [hx]
    · calc
        _ ≤ (⌊x⌋ : ℚ) + (rowOffset x + w) :=
          add_le_add_right (show min (1 : ℚ) (rowOffset x + w) ≤ rowOffset x + w from min_le_right _ _) (⌊x⌋ : ℚ)
        _ = _ := by rw [← add_assoc, hx]
  · simp only [rowFragment, if_true] at hpos ⊢
    have htail : 0 < rowOffset x + w - 1 := by
      by_contra! ht
      exact (not_lt_of_ge (max_le (le_refl (0 : ℚ)) ht)) hpos
    rw [max_eq_right (le_of_lt htail)]
    push_cast
    have hfloor := Int.lt_floor_add_one x
    exact ⟨le_of_lt (by linarith), by linarith only [hx]⟩

theorem rowFragment_machine_separation {x y w v : ℚ} {tx ty : Bool}
    (horder : x + w ≤ y)
    (hx : (rowFragment x w tx).first < (rowFragment x w tx).last)
    (hy : (rowFragment y v ty).first < (rowFragment y v ty).last)
    (hr : (rowFragment x w tx).row = (rowFragment y v ty).row) :
    (rowFragment x w tx).last ≤ (rowFragment y v ty).first := by
  have h := (rowFragment_contained hx).2.trans (horder.trans (rowFragment_contained hy).1)
  rwa [hr, add_le_add_iff_left] at h

theorem rowFragment_machine_bound {x w : ℚ} {tail : Bool}
    (hx : 0 ≤ x) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {m : ℕ}
    (hbudget : x + w ≤ (m : ℚ))
    (hpos : (rowFragment x w tail).first < (rowFragment x w tail).last) :
    (rowFragment x w tail).row.toNat < m := by
  have hr := rowFragment_row_nonneg (w := w) hx tail
  have hrow : (((rowFragment x w tail).row.toNat : ℕ) : ℚ) =
      ((rowFragment x w tail).row : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hr
  have hfirst := (rowFragment_interval x w hw0 hw1 tail).1
  have hlast := (rowFragment_contained hpos).2
  have : (((rowFragment x w tail).row.toNat : ℕ) : ℚ) < (m : ℚ) := by
    rw [hrow]
    linarith
  exact_mod_cast this

end TBB
