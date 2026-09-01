/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PartitionZheng.Meta.Attr

/-!
# The inner integral

The area integral of the lattice count reduces, after the substitutions
`a = sqrt Y * α` and `t = a * σ`, to an inner integral in `α` over the range
where the integrand is positive, namely `0 ≤ α < (4 - σ²)^{-1/2}`. Writing
`c = 4 - σ²` and `A = c^{-1/2}`, so that `c * A ^ 2 = 1`, that integral is

`∫_0^A (1 - c α²) dα = A - c A³/3 = A - A/3 = 2A/3`.

## Main results

* `PartitionZheng.integral_one_sub_const_mul_sq` — the polynomial integral.
* `PartitionZheng.inner_integral` — its value `2 * A / 3` when `c * A ^ 2 = 1`.
-/

@[expose] public section

namespace PartitionZheng

/-- The polynomial integral, with no relation assumed between `c` and `A`. -/
theorem integral_one_sub_const_mul_sq (c A : ℝ) :
    (∫ α in (0 : ℝ)..A, (1 - c * α ^ 2)) = A - c * A ^ 3 / 3 := by
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 A :=
    intervalIntegrable_const
  have hsq : IntervalIntegrable (fun α : ℝ => c * α ^ 2) MeasureTheory.volume 0 A :=
    (intervalIntegral.intervalIntegrable_pow 2).const_mul c
  rw [intervalIntegral.integral_sub hone hsq, intervalIntegral.integral_const_mul]
  simp
  ring

/-- With `c * A ^ 2 = 1`, the inner integral is `2 * A / 3`. This is the
`(2/3) * (4 - σ²)^{-1/2}` of the source. -/
@[pz_tag "lem_inner_integral"]
theorem inner_integral {c A : ℝ} (h : c * A ^ 2 = 1) :
    (∫ α in (0 : ℝ)..A, (1 - c * α ^ 2)) = 2 * A / 3 := by
  rw [integral_one_sub_const_mul_sq]
  have hcube : c * A ^ 3 = A := by
    calc c * A ^ 3 = (c * A ^ 2) * A := by ring
      _ = A := by rw [h]; ring
  rw [show c * A ^ 3 / 3 = A / 3 by rw [hcube]]
  ring

/-- The area function of the lattice count:
`F_Y a = (1 / (24 a)) * ∫_{-a}^{a} (Y + t² - 4a²)_+ dt`, where `x_+ = max x 0`.
Its integral over `a > 0` is what produces the `pi / 108` of the class-number
average. -/
@[pz_tag "def_F"]
noncomputable def areaF (Y a : ℝ) : ℝ :=
  (1 / (24 * a)) * ∫ t in (-a)..a, max (Y + t ^ 2 - 4 * a ^ 2) 0

end PartitionZheng
