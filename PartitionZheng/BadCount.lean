/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import PartitionZheng.Constants
public import PartitionZheng.Range

/-!
# Few discriminants have a large class number

A discriminant is *bad* for the threshold `H` when its class number exceeds
`H * sqrt Y`, the complement in `admissible Y` of the good ones. Since every bad
discriminant contributes more than `H * sqrt Y` to `∑_{D ∈ D(Y)} h(D)` and all
terms of that sum are nonnegative, the class-number average bounds the number of
bad discriminants: dividing `(beta + ε H) Y ^ (3/2)` by `H sqrt Y` leaves
`(beta / H + ε) Y`.

`Y ^ (3/2)` is written `Y * sqrt Y`, as in `PartitionZheng.ZH`.

## Main definitions

* `PartitionZheng.bad` — the bad discriminants up to `Y`.

## Main results

* `PartitionZheng.bad_count` — `#bad(Y,H) ≤ (beta / H + ε) Y` for `Y` large.
-/

@[expose] public section

namespace PartitionZheng

open Real

open Classical in
/-- The bad discriminants up to `Y`: those whose class number exceeds
`H * sqrt Y`. This is the complement in `admissible Y` of `good Y H`. -/
noncomputable def bad (Y H : ℝ) : Finset ℕ :=
  (admissible Y).filter fun D => (H * Real.sqrt Y < (classNumber (D : ℤ) : ℝ))

/-- A natural number lies in `bad Y H` exactly when it is admissible up to `Y`
and its class number exceeds `H * sqrt Y`. -/
theorem mem_bad_iff {Y H : ℝ} {D : ℕ} :
    D ∈ bad Y H ↔ D ∈ admissible Y ∧ (H * Real.sqrt Y < (classNumber (D : ℤ) : ℝ)) := by
  classical
  simp [bad, Finset.mem_filter]

/-- Every admissible discriminant is good or bad, so the two counts together
cover `#D(Y)`. -/
theorem card_admissible_le_card_good_add_card_bad {Y H : ℝ} :
    (admissible Y).card ≤ (good Y H).card + (bad Y H).card := by
  classical
  calc (admissible Y).card ≤ (good Y H ∪ bad Y H).card := by
        refine Finset.card_le_card ?_
        intro D hD
        rcases le_or_gt ((classNumber (D : ℤ) : ℝ)) (H * Real.sqrt Y) with h | h
        · exact Finset.mem_union_left _ (mem_good_iff.mpr ⟨hD, h⟩)
        · exact Finset.mem_union_right _ (mem_bad_iff.mpr ⟨hD, h⟩)
    _ ≤ (good Y H).card + (bad Y H).card := Finset.card_union_le _ _

/-- The bad discriminants each contribute more than `H * sqrt Y` to the
class-number sum over `admissible Y`, whose other terms are nonnegative. -/
theorem card_bad_mul_le_sum {Y H : ℝ} :
    ((bad Y H).card : ℝ) * (H * Real.sqrt Y)
      ≤ ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) := by
  classical
  calc ((bad Y H).card : ℝ) * (H * Real.sqrt Y)
      = (bad Y H).card • (H * Real.sqrt Y) := by rw [nsmul_eq_mul]
    _ ≤ ∑ D ∈ bad Y H, (classNumber (D : ℤ) : ℝ) := by
        refine Finset.card_nsmul_le_sum _ _ _ ?_
        intro D hD
        exact le_of_lt (mem_bad_iff.mp hD).2
    _ ≤ ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro D _ _
        positivity

/-- **`lem_bad_count`.** For every `ε > 0` the number of discriminants up to `Y`
whose class number exceeds `H * sqrt Y` is at most `(beta / H + ε) * Y`, once
`Y` is large.

The hypothesis `hclass` asserts the class-number average: for every `ε > 0`,
`∑_{D ∈ D(Y)} h(D) ≤ (beta + ε) Y ^ (3/2)` once `Y` is large. -/
@[pz_tag "lem_bad_count"]
theorem bad_count {H : ℝ} (hH : 0 < H)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ((bad Y H).card : ℝ) ≤ (beta / H + ε) * Y := by
  obtain ⟨Y₀, hY₀, hbound⟩ := hclass (ε * H) (by positivity)
  refine ⟨Y₀, hY₀, fun Y hY => ?_⟩
  have hY2 : (2 : ℝ) ≤ Y := le_trans hY₀ hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hK : 0 < H * Real.sqrt Y := by positivity
  have hne : H ≠ 0 := ne_of_gt hH
  have hrw : (beta / H + ε) * Y * (H * Real.sqrt Y)
      = (beta + ε * H) * (Y * Real.sqrt Y) := by
    field_simp
  refine le_of_mul_le_mul_right ?_ hK
  rw [hrw]
  exact le_trans card_bad_mul_le_sum (hbound Y hY)

end PartitionZheng
