/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.ClassAverage
public import PartitionZheng.FIntegral
public import PartitionZheng.PartialSummation
public import PartitionZheng.TripleCount

/-!
# Discharging the explicit hypotheses

Several results in this development are stated with their dependencies as
explicit hypotheses. Those hypotheses are discharged here, leaving statements
that depend on nothing but the parity theorem.

Two of them are phrased differently on the two sides and need a conversion
rather than a direct application:

* `exists_const_card_pairs_le` states its range condition as `3 a² ≤ Y`, while
  `class_average` states it as `a ≤ √(Y/3)`. The two are equivalent for `a ≥ 1`;
  `three_sq_le_of_sqrt` converts.
* `exists_weighted_areaF_sum_le` assumes the integral bound written with the
  literal `π / 108`, while `integral_areaF` writes it with `beta`. These are
  definitionally equal.

## Main results

* `PartitionZheng.exists_weighted_areaF_sum_le_unconditional` — the weighted sum of
  the areas `areaF Y a` bounded by `π / 108 * Y √Y + C * Y log Y`.
* `PartitionZheng.class_average_unconditional` — the class numbers of the admissible
  discriminants up to `Y` sum to at most `(beta + ε) * Y √Y` for all large `Y`.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- For `a ≥ 1`, `a ≤ √(Y/3)` gives `3 a² ≤ Y`. -/
theorem three_sq_le_of_sqrt {Y : ℝ} {a : ℤ} (ha : 1 ≤ a)
    (h : (a : ℝ) ≤ Real.sqrt (Y / 3)) : 3 * (a : ℝ) ^ 2 ≤ Y := by
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hs : (0 : ℝ) ≤ Real.sqrt (Y / 3) := Real.sqrt_nonneg _
  have hY3 : (0 : ℝ) ≤ Y / 3 := by
    by_contra hc
    rw [Real.sqrt_eq_zero_of_nonpos (by linarith : Y / 3 ≤ 0)] at h
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hsq : Real.sqrt (Y / 3) ^ 2 = Y / 3 := Real.sq_sqrt hY3
  nlinarith

/-- `exists_weighted_areaF_sum_le` with its hypothesis discharged from
`integral_areaF`: the two state the same integral bound, one writing `π / 108`
where the other writes `beta`, and those are definitionally equal. -/
theorem exists_weighted_areaF_sum_le_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
        ≤ Real.pi / 108 * (Y * Real.sqrt Y) + C * (Y * Real.log Y) := by
  refine exists_weighted_areaF_sum_le ?_
  intro Y hY
  have h := integral_areaF hY
  unfold beta at h
  exact h

/-- `class_average` with both of its hypotheses discharged: for every `ε > 0`,
the class numbers of the admissible discriminants up to `Y` sum to at most
`(beta + ε) * Y √Y` once `Y` is large enough. -/
theorem class_average_unconditional :
    ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y) := by
  refine class_average ?_ exists_weighted_areaF_sum_le_unconditional
  obtain ⟨C, hC, hbound⟩ := exists_const_card_pairs_le
  refine ⟨C, hC, fun Y hY a ha hsqrt => ?_⟩
  exact hbound Y hY a ha (three_sq_le_of_sqrt ha hsqrt)

end PartitionZheng
