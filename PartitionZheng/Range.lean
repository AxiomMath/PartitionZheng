/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Monotone.Basic
public import PartitionZheng.Discriminants
public import PartitionZheng.Forms

/-!
# The range bound and the good discriminants

For a threshold `H`, a discriminant is *good* when its class number is at most
`H * sqrt Y`; the parity theorem then gives an admissible `m ≤ 12 * H * sqrt Y + 2`,
so the resulting partition index is at most

`Z_H Y = 6 H² Y² + 2 H Y^{3/2} + Y/6 + 1/24`.

`Y ^ (3/2)` is written `Y * sqrt Y`, which agrees with it for `Y ≥ 0` — the only
range where `Z_H` is used — and avoids `rpow`.

## Main definitions

* `PartitionZheng.good` — the good discriminants up to `Y`.
* `PartitionZheng.ZH` — the range bound `Z_H Y`.

## Main results

* `PartitionZheng.ZH_strictMonoOn` — `Z_H` is strictly increasing on `[0, ∞)`,
  which is what makes the change of variable `Z_H Y_X = X` well posed.
-/

@[expose] public section

namespace PartitionZheng

open Real

open Classical in
/-- The good discriminants up to `Y`: those whose class number is at most
`H * sqrt Y`. -/
@[pz_tag "def_Good"]
noncomputable def good (Y H : ℝ) : Finset ℕ :=
  (admissible Y).filter fun D => ((classNumber (D : ℤ) : ℝ) ≤ H * Real.sqrt Y)

/-- The range bound: every partition index produced by a good discriminant up to
`Y` is at most `ZH H Y`. -/
@[pz_tag "def_ZH"]
noncomputable def ZH (H Y : ℝ) : ℝ :=
  6 * H ^ 2 * Y ^ 2 + 2 * H * (Y * Real.sqrt Y) + Y / 6 + 1 / 24

/-- `ZH H` is strictly increasing on `[0, ∞)`. The quadratic and the `Y^{3/2}`
term are increasing there, and the linear term `Y / 6` is strictly increasing,
so the sum is. -/
@[pz_tag "lem_ZH_mono"]
theorem ZH_strictMonoOn {H : ℝ} (hH : 0 < H) :
    StrictMonoOn (ZH H) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy.le
  have hxs : x * Real.sqrt x ≤ y * Real.sqrt y := by
    have h1 : x * Real.sqrt x ≤ y * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hxy.le (Real.sqrt_nonneg x)
    have h2 : y * Real.sqrt x ≤ y * Real.sqrt y :=
      mul_le_mul_of_nonneg_left hs hy0
    linarith
  have hH2 : 0 ≤ 6 * H ^ 2 := by positivity
  unfold ZH
  have hq : 6 * H ^ 2 * x ^ 2 ≤ 6 * H ^ 2 * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hH2
  have hc : 2 * H * (x * Real.sqrt x) ≤ 2 * H * (y * Real.sqrt y) :=
    mul_le_mul_of_nonneg_left hxs (by linarith)
  linarith

/-- `D` is good for `Y` and `H` exactly when it is admissible up to `Y` and its class
number is at most `H * sqrt Y`. -/
theorem mem_good_iff {Y H : ℝ} {D : ℕ} :
    D ∈ good Y H ↔ D ∈ admissible Y ∧ ((classNumber (D : ℤ) : ℝ) ≤ H * Real.sqrt Y) := by
  classical
  simp [good, Finset.mem_filter]

/-- The partition index produced by a discriminant `D ≤ Y` whose admissible `m`
satisfies `m ≤ 12 H sqrt Y + 2` is at most `ZH H Y`. Expanding
`(12 H sqrt Y + 2) ^ 2 = 144 H² Y + 48 H sqrt Y + 4` and multiplying by `Y`
gives exactly the four terms of `ZH`. -/
@[pz_tag "lem_nD_bound"]
theorem nD_le_ZH {Y H : ℝ} (hY : 0 ≤ Y) {D m n : ℕ}
    (hDY : (D : ℝ) ≤ Y) (hmle : (m : ℝ) ≤ 12 * H * Real.sqrt Y + 2)
    (hn : 24 * n = D * m ^ 2 + 1) : (n : ℝ) ≤ ZH H Y := by
  have hs : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hs0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hcast : (24 : ℝ) * (n : ℝ) = (D : ℝ) * (m : ℝ) ^ 2 + 1 := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hn
    push_cast at this
    linarith
  have hmsq : (m : ℝ) ^ 2 ≤ (12 * H * Real.sqrt Y + 2) ^ 2 := by
    have h2 : (0 : ℝ) ≤ 12 * H * Real.sqrt Y + 2 := le_trans hm0 hmle
    nlinarith
  have hDm : (D : ℝ) * (m : ℝ) ^ 2 ≤ Y * (12 * H * Real.sqrt Y + 2) ^ 2 := by
    have hsq0 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
    nlinarith
  have hexp : Y * (12 * H * Real.sqrt Y + 2) ^ 2
      = 144 * H ^ 2 * Y ^ 2 + 48 * H * (Y * Real.sqrt Y) + 4 * Y := by
    have hsq : (12 * H * Real.sqrt Y + 2) ^ 2
        = 144 * H ^ 2 * Real.sqrt Y ^ 2 + 48 * H * Real.sqrt Y + 4 := by ring
    rw [hsq, hs]
    ring
  rw [hexp] at hDm
  unfold ZH
  linarith

/-- `ZH H` is continuous. -/
theorem ZH_continuous {H : ℝ} : Continuous (ZH H) := by
  unfold ZH
  have : Continuous (fun Y : ℝ => Real.sqrt Y) := Real.continuous_sqrt
  fun_prop

/-- `ZH H` is injective on `[0, ∞)`. -/
theorem ZH_injOn {H : ℝ} (hH : 0 < H) : Set.InjOn (ZH H) (Set.Ici 0) :=
  (ZH_strictMonoOn hH).injOn

/-- The change of variable is well posed: for `X ≥ ZH H 0` there is exactly one
`Y ≥ 0` with `ZH H Y = X`. Existence is the intermediate value theorem on
`[0, 6X]`, using `ZH H Y ≥ Y / 6`; uniqueness is strict monotonicity. -/
@[pz_tag "lem_YX_exists"]
theorem exists_unique_YX {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    ∃! Y, 0 ≤ Y ∧ ZH H Y = X := by
  have hZH0 : ZH H 0 = 1 / 24 := by unfold ZH; norm_num
  have hX0 : (0 : ℝ) ≤ X := by rw [hZH0] at hX; linarith
  have hB6 : (0 : ℝ) ≤ 6 * X := by linarith
  have hB : X ≤ ZH H (6 * X) := by
    unfold ZH
    have h1 : (0 : ℝ) ≤ 6 * H ^ 2 * (6 * X) ^ 2 := by positivity
    have hs : (0 : ℝ) ≤ Real.sqrt (6 * X) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * H * ((6 * X) * Real.sqrt (6 * X)) := by
      have : (0 : ℝ) ≤ (6 * X) * Real.sqrt (6 * X) := mul_nonneg hB6 hs
      positivity
    linarith
  have hcont : ContinuousOn (ZH H) (Set.Icc 0 (6 * X)) :=
    ZH_continuous.continuousOn
  have hsub := intermediate_value_Icc hB6 hcont
  have hmem : X ∈ Set.Icc (ZH H 0) (ZH H (6 * X)) := ⟨hX, hB⟩
  obtain ⟨Y, hYmem, hYeq⟩ := hsub hmem
  refine ⟨Y, ⟨hYmem.1, hYeq⟩, ?_⟩
  rintro Z ⟨hZ0, hZeq⟩
  exact ZH_injOn hH hZ0 hYmem.1 (by rw [hZeq, hYeq])

end PartitionZheng
