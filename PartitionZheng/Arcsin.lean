/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PartitionZheng.Meta.Attr

/-!
# The arcsine integral

After the substitutions of the lattice count, the outer integral is
`∫_{-1}^{1} (4 - σ²)^{-1/2} dσ`, which is `π / 3`. The antiderivative is
`arcsin (σ / 2)`: by the chain rule its derivative is
`(1/2) * (1 - (σ/2)²)^{-1/2}`, and `√(1 - σ²/4) = √(4 - σ²) / 2`, so that is
`(4 - σ²)^{-1/2}`.

Mathlib has `arcsin 1 = π / 2` but not `arcsin (1/2) = π / 6`, so that is proved
here from `sin (π / 6) = 1 / 2`.

## Main results

* `PartitionZheng.arcsin_half` — `arcsin (1/2) = π / 6`.
* `PartitionZheng.arcsin_integral` — `∫_{-1}^{1} (4 - σ²)^{-1/2} dσ = π / 3`.
-/

@[expose] public section

namespace PartitionZheng

open Real intervalIntegral

/-- `arcsin (1/2) = π / 6`, from `sin (π / 6) = 1 / 2`. -/
theorem arcsin_half : Real.arcsin (1 / 2) = π / 6 := by
  have hpi := Real.pi_pos
  have h : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
  rw [← h, Real.arcsin_sin (by linarith) (by linarith)]

/-- `√(4 - σ²) = 2 * √(1 - σ² / 4)`, the algebra that identifies the chain-rule
derivative with the integrand. -/
theorem sqrt_four_sub_sq {σ : ℝ} (h : σ ^ 2 ≤ 4) :
    Real.sqrt (4 - σ ^ 2) = 2 * Real.sqrt (1 - σ ^ 2 / 4) := by
  have h4 : (0 : ℝ) ≤ 1 - σ ^ 2 / 4 := by linarith
  have : (4 : ℝ) - σ ^ 2 = 4 * (1 - σ ^ 2 / 4) := by ring
  rw [this, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  rw [show Real.sqrt 4 = 2 by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]

/-- On `|σ| ≤ 1`, the function `σ ↦ arcsin (σ / 2)` has derivative
`(4 - σ²)^{-1/2}`. -/
theorem hasDerivAt_arcsin_half {σ : ℝ} (h : |σ| ≤ 1) :
    HasDerivAt (fun s : ℝ => Real.arcsin (s / 2)) (1 / Real.sqrt (4 - σ ^ 2)) σ := by
  have habs : |σ / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hne1 : σ / 2 ≠ 1 := by
    intro hc; rw [hc] at habs; norm_num at habs
  have hne2 : σ / 2 ≠ -1 := by
    intro hc; rw [hc] at habs; norm_num at habs
  have hinner : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) σ := by
    simpa using (hasDerivAt_id σ).div_const 2
  -- `.comp` yields `arcsin ∘ (· / 2)`; Lean will not higher-order-unify that
  -- with the lambda, so rewrite the composition rather than ascribing a type.
  have hchain := (Real.hasDerivAt_arcsin hne2 hne1).comp σ hinner
  rw [Function.comp_def] at hchain
  have hsq : σ ^ 2 ≤ 4 := by nlinarith [abs_le.mp h]
  have hpos : (0 : ℝ) < 1 - (σ / 2) ^ 2 := by nlinarith [abs_le.mp habs]
  have hkey : 1 / Real.sqrt (1 - (σ / 2) ^ 2) * (1 / 2)
      = 1 / Real.sqrt (4 - σ ^ 2) := by
    have hrw : (σ / 2) ^ 2 = σ ^ 2 / 4 := by ring
    rw [hrw, sqrt_four_sub_sq hsq]
    have hs : (0 : ℝ) < Real.sqrt (1 - σ ^ 2 / 4) := by
      apply Real.sqrt_pos.mpr; rw [← hrw]; exact hpos
    field_simp
  rw [hkey] at hchain
  exact hchain

/-- `∫_{-1}^{1} (4 - σ²)^{-1/2} dσ = π / 3`. -/
@[pz_tag "lem_arcsin_integral"]
theorem arcsin_integral :
    (∫ σ in (-1 : ℝ)..1, 1 / Real.sqrt (4 - σ ^ 2)) = π / 3 := by
  have hcont : ContinuousOn (fun σ : ℝ => 1 / Real.sqrt (4 - σ ^ 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
    · intro σ hσ
      have hσ' : |σ| ≤ 1 := by
        rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hσ
        exact abs_le.mpr ⟨hσ.1, hσ.2⟩
      have : σ ^ 2 ≤ 1 := by nlinarith [abs_le.mp hσ']
      have : (0 : ℝ) < 4 - σ ^ 2 := by linarith
      exact ne_of_gt (Real.sqrt_pos.mpr this)
  have hderiv : ∀ σ ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.arcsin (s / 2)) (1 / Real.sqrt (4 - σ ^ 2)) σ := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hσ
    exact hasDerivAt_arcsin_half (abs_le.mpr ⟨hσ.1, hσ.2⟩)
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have h1 : Real.arcsin ((1 : ℝ) / 2) = π / 6 := arcsin_half
  have h2 : Real.arcsin ((-1 : ℝ) / 2) = -(π / 6) := by
    rw [show ((-1 : ℝ) / 2) = -(1 / 2) by ring, Real.arcsin_neg, h1]
  rw [h1, h2]
  ring

end PartitionZheng
