/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PartitionZheng.Meta.Attr

/-!
# Comparing a step-`6` sum with an integral

The lattice count sums over the odd `b` with `|b| ≤ a`, grouped by `b` modulo
`6`. Each group is an arithmetic progression of step `6`, and the count is
compared with the corresponding integral. Mathlib's
`Mathlib.Analysis.SumIntegralComparisons` provides the step-`1` comparisons; the
step-`6` versions below come from substituting `u ↦ p + 6u`, whose interval
integral rescales by `intervalIntegral.mul_integral_comp_add_mul`:

`6 * ∫ x in 0..n, f (p + 6 * x) = ∫ x in p..p + 6 * n, f x`.

Both one-sided comparisons are recorded, since the error term of the lattice
count needs the sum trapped on both sides. Their difference is a boundary term
`f (p + 6n) - f p`, which for the lattice count is `O(Y/a)` — the source's error.

## Main results

* `PartitionZheng.sum_step_six_le_integral` — monotone: sum below the integral.
* `PartitionZheng.integral_le_sum_step_six` — monotone: integral below the
  shifted sum.
-/

@[expose] public section

namespace PartitionZheng

open Finset intervalIntegral

/-- Reindexing a step-`6` progression as a step-`1` one preserves monotonicity. -/
private theorem monotoneOn_comp_step_six {f : ℝ → ℝ} {p : ℝ} {n : ℕ}
    (hf : MonotoneOn f (Set.Icc p (p + 6 * (n : ℝ)))) :
    MonotoneOn (fun u : ℝ => f (p + 6 * u)) (Set.Icc 0 (0 + (n : ℝ))) := by
  intro u hu v hv huv
  simp only [zero_add, Set.mem_Icc] at hu hv
  refine hf ?_ ?_ (by linarith)
  · exact Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · exact Set.mem_Icc.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- The step-`6` integral rescaling: the integral of `u ↦ f (p + 6u)` over
`[0, n]` is a sixth of the integral of `f` over `[p, p + 6n]`. -/
theorem integral_step_six (f : ℝ → ℝ) (p : ℝ) (n : ℕ) :
    (∫ u in (0 : ℝ)..(n : ℝ), f (p + 6 * u))
      = (1 / 6) * ∫ x in p..(p + 6 * (n : ℝ)), f x := by
  have h := intervalIntegral.mul_integral_comp_add_mul
    (f := f) (a := (0 : ℝ)) (b := (n : ℝ)) (c := (6 : ℝ)) (d := p)
  -- `h : 6 * ∫ u in 0..n, f (p + 6 * u) = ∫ x in p + 6 * 0..p + 6 * n, f x`
  rw [show p + 6 * (0 : ℝ) = p by ring] at h
  linarith [h]

/-- **Monotone, sum below integral.** For `f` monotone on `[p, p + 6n]`, the
step-`6` sum starting at `p` is at most a sixth of the integral. -/
theorem sum_step_six_le_integral {f : ℝ → ℝ} {p : ℝ} {n : ℕ}
    (hf : MonotoneOn f (Set.Icc p (p + 6 * (n : ℝ)))) :
    ∑ i ∈ Finset.range n, f (p + 6 * (i : ℝ))
      ≤ (1 / 6) * ∫ x in p..(p + 6 * (n : ℝ)), f x := by
  have hg := monotoneOn_comp_step_six hf
  have hsum := MonotoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := n)
    (f := fun u : ℝ => f (p + 6 * u)) hg
  simp only [zero_add] at hsum
  rw [integral_step_six f p n] at hsum
  exact hsum

/-- **Monotone, integral below shifted sum.** For `f` monotone on
`[p, p + 6n]`, a sixth of the integral is at most the step-`6` sum taken at the
right endpoints. Together with `sum_step_six_le_integral` this traps the sum
within the boundary term `f (p + 6n) - f p`. -/
theorem integral_le_sum_step_six {f : ℝ → ℝ} {p : ℝ} {n : ℕ}
    (hf : MonotoneOn f (Set.Icc p (p + 6 * (n : ℝ)))) :
    (1 / 6) * (∫ x in p..(p + 6 * (n : ℝ)), f x)
      ≤ ∑ i ∈ Finset.range n, f (p + 6 * ((i : ℝ) + 1)) := by
  have hg := monotoneOn_comp_step_six hf
  have hint := MonotoneOn.integral_le_sum (x₀ := (0 : ℝ)) (a := n)
    (f := fun u : ℝ => f (p + 6 * u)) hg
  simp only [zero_add] at hint
  rw [integral_step_six f p n] at hint
  have hcast : ∑ x ∈ Finset.range n, f (p + 6 * ((x + 1 : ℕ) : ℝ))
      = ∑ i ∈ Finset.range n, f (p + 6 * ((i : ℝ) + 1)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    norm_num
  rw [hcast] at hint
  exact hint

/-- The interval-length function of the lattice count,
`L⁺(t) = (Y + t² - 4a²)₊ / (4a)`. This is the integrand of `def_F` divided by
`4a`, and `card_c_le` bounds the outer-coefficient count by a multiple of it. -/
noncomputable def Lplus (Y a t : ℝ) : ℝ :=
  max (Y + t ^ 2 - 4 * a ^ 2) 0 / (4 * a)

/-- `L⁺` is even, so the two halves of `[-a, a]` mirror each other. -/
theorem Lplus_neg (Y a t : ℝ) : Lplus Y a (-t) = Lplus Y a t := by
  unfold Lplus
  rw [neg_pow_two]

/-- `L⁺` is monotone on `[0, ∞)`: `t²` increases there and `max`/division by
`4a > 0` preserve the order. -/
theorem Lplus_monotoneOn {Y a : ℝ} (ha : 0 < a) :
    MonotoneOn (Lplus Y a) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  have ha4 : (0 : ℝ) < 4 * a := by linarith
  have hsq : u ^ 2 ≤ v ^ 2 := by nlinarith
  unfold Lplus
  apply div_le_div_of_nonneg_right ?_ ha4.le
  exact max_le_max (by linarith) (le_refl 0)

/-- `L⁺` is antitone on `(-∞, 0]`, by evenness. -/
theorem Lplus_antitoneOn {Y a : ℝ} (ha : 0 < a) :
    AntitoneOn (Lplus Y a) (Set.Iic 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Iic] at hu hv
  rw [← Lplus_neg Y a u, ← Lplus_neg Y a v]
  exact Lplus_monotoneOn ha (Set.mem_Ici.mpr (by linarith))
    (Set.mem_Ici.mpr (by linarith)) (by linarith)

/-- The boundary term controlling the sum-to-integral error: on `[0, a]` the
total variation of `L⁺` is `L⁺(a) - L⁺(0) ≤ Y / (4a)`.

This is the source's `O(Y/a)`, with the constant exhibited: `1/4`. -/
theorem Lplus_variation_le {Y a : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) :
    Lplus Y a a - Lplus Y a 0 ≤ Y / (4 * a) := by
  have ha4 : (0 : ℝ) < 4 * a := by linarith
  have hnn : 0 ≤ Lplus Y a 0 := by
    unfold Lplus
    exact div_nonneg (le_max_right _ _) ha4.le
  have hub : Lplus Y a a ≤ Y / (4 * a) := by
    unfold Lplus
    apply div_le_div_of_nonneg_right ?_ ha4.le
    apply max_le
    · nlinarith
    · exact hY
  linarith

end PartitionZheng
