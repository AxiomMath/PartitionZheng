/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import PartitionZheng.Arcsin
public import PartitionZheng.Constants
public import PartitionZheng.Integrals
public import PartitionZheng.SumIntegral

/-!
# The area integral

The area integral is `∫_0^∞ F_Y(a) da = (π/108) Y^{3/2}`. The argument
substitutes `t = aσ` in the inner integral, then `a = √Y α` in the outer one,
exchanges the order of integration, and evaluates the inner `α`-integral with
`inner_integral` and the resulting `σ`-integral with `arcsin_integral`.

After the two substitutions all the `Y` dependence sits in a prefactor `Y/24`
and the remaining double integral is a pure number — which is what produces the
constant `π/108`.

The improper outer integral is a `MeasureTheory.integral` over `Set.Ioi 0`
rather than an `intervalIntegral`. Since the integrand
`(α, σ) ↦ (1 - (4 - σ²)α²)_+` is nonnegative and vanishes off the bounded set
`(0, 1] × (-1, 1]`, it is integrable on the product and the exchange of order is
`MeasureTheory.integral_integral_swap`; no integrability hypothesis on the
improper integral itself is needed.

`Y ^ (3/2)` is written `Y * sqrt Y`: the two agree for `Y ≥ 0`, and the
hypothesis here is `0 < Y`.

## Main results

* `PartitionZheng.areaF_subst` — `F_Y(a) = (1/24) ∫_{-1}^{1} (Y + a²σ² - 4a²)_+ dσ`.
* `PartitionZheng.areaF_scaled` — `F_Y(√Y α) = (Y/24) ∫_{-1}^{1} (1 - (4-σ²)α²)_+ dσ`.
* `PartitionZheng.integral_areaF` — `∫_0^∞ F_Y(a) da = β Y^{3/2}`.
-/

@[expose] public section

namespace PartitionZheng

open intervalIntegral MeasureTheory Real

/-- **The inner substitution.** For `a > 0`,

`F_Y(a) = (1/24) ∫_{-1}^{1} (Y + a²σ² - 4a²)_+ dσ`.

Substituting `t = aσ` scales the integral by `a`, which cancels the `1/(24a)`
prefactor of `areaF`. The interval becomes `[-1, 1]`, independent of `a`, so the
region of integration is a product and the order of integration can later be
exchanged. -/
theorem areaF_subst {Y a : ℝ} (ha : 0 < a) :
    areaF Y a = (1 / 24) * ∫ σ in (-1 : ℝ)..1, max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0 := by
  have hane : a ≠ 0 := ne_of_gt ha
  -- `a * ∫_{-1}^{1} f (a σ) dσ = ∫_{-a}^{a} f`
  have h := intervalIntegral.mul_integral_comp_add_mul
    (f := fun t : ℝ => max (Y + t ^ 2 - 4 * a ^ 2) 0)
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (c := a) (d := (0 : ℝ))
  rw [show (0 : ℝ) + a * (-1) = -a by ring, show (0 : ℝ) + a * 1 = a by ring] at h
  -- rewrite the integrand of the scaled integral
  have hint : (∫ σ in (-1 : ℝ)..1, max (Y + (0 + a * σ) ^ 2 - 4 * a ^ 2) 0)
      = ∫ σ in (-1 : ℝ)..1, max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0 := by
    refine intervalIntegral.integral_congr ?_
    intro σ _
    -- `integral_congr` leaves the integrands un-beta-reduced
    change max (Y + (0 + a * σ) ^ 2 - 4 * a ^ 2) 0
      = max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0
    rw [show (0 + a * σ) ^ 2 = a ^ 2 * σ ^ 2 by ring]
  rw [hint] at h
  -- `F_Y(a) = (1/(24a)) * (a * J) = J/24`
  unfold areaF
  rw [← h]
  field_simp

/-- **The outer substitution.** For `Y > 0` and `α > 0`,

`F_Y(√Y α) = (Y/24) ∫_{-1}^{1} (1 - (4 - σ²) α²)₊ dσ`.

With `a = √Y α` we have `a² = Y α²`, so
`Y + a²σ² - 4a² = Y (1 - (4 - σ²) α²)` and the positive part scales out of the
whole expression. The `Y` dependence is now entirely in the prefactor: the
remaining double integral is a pure number, which is what produces the constant
`π/108` after the two evaluations. -/
theorem areaF_scaled {Y α : ℝ} (hY : 0 < Y) (hα : 0 < α) :
    areaF Y (Real.sqrt Y * α)
      = (Y / 24) * ∫ σ in (-1 : ℝ)..1, max (1 - (4 - σ ^ 2) * α ^ 2) 0 := by
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have ha : 0 < Real.sqrt Y * α := mul_pos hsY hα
  rw [areaF_subst ha]
  have hsq : (Real.sqrt Y * α) ^ 2 = Y * α ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hY.le]
  have hint : (∫ σ in (-1 : ℝ)..1,
        max (Y + (Real.sqrt Y * α) ^ 2 * σ ^ 2 - 4 * (Real.sqrt Y * α) ^ 2) 0)
      = ∫ σ in (-1 : ℝ)..1, Y * max (1 - (4 - σ ^ 2) * α ^ 2) 0 := by
    refine intervalIntegral.integral_congr ?_
    intro σ _
    -- `integral_congr` leaves the integrands un-beta-reduced
    change max (Y + (Real.sqrt Y * α) ^ 2 * σ ^ 2 - 4 * (Real.sqrt Y * α) ^ 2) 0
      = Y * max (1 - (4 - σ ^ 2) * α ^ 2) 0
    rw [hsq, show Y + Y * α ^ 2 * σ ^ 2 - 4 * (Y * α ^ 2)
          = Y * (1 - (4 - σ ^ 2) * α ^ 2) by ring]
    -- the positive part scales out, by cases on the sign
    rcases le_or_gt 0 (1 - (4 - σ ^ 2) * α ^ 2) with h | h
    · rw [max_eq_left h, max_eq_left (by positivity :
        (0 : ℝ) ≤ Y * (1 - (4 - σ ^ 2) * α ^ 2))]
    · rw [max_eq_right (le_of_lt h),
        max_eq_right (by nlinarith : Y * (1 - (4 - σ ^ 2) * α ^ 2) ≤ 0)]
      ring
  rw [hint, intervalIntegral.integral_const_mul]
  ring

/-- **The outer substitution, as a set integral.** `areaF_scaled` restated with a
`MeasureTheory` set integral over `Set.Ioc (-1) 1` in place of the interval
integral.

The exchange of integration order needs `MeasureTheory.integral` over
`Set.Ioi 0` in the outer variable and a Tonelli argument for the nonnegative
integrand; `intervalIntegral` — which both substitutions above are stated in —
does not reach it. `intervalIntegral.integral_of_le` is the conversion, valid
because `-1 ≤ 1`. -/
theorem areaF_scaled_setIntegral {Y α : ℝ} (hY : 0 < Y) (hα : 0 < α) :
    areaF Y (Real.sqrt Y * α)
      = (Y / 24) * ∫ σ in Set.Ioc (-1 : ℝ) 1, max (1 - (4 - σ ^ 2) * α ^ 2) 0 := by
  rw [areaF_scaled hY hα,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-! ### The integrand of the double integral

The exchange of integration order needs the integrand
`(α, σ) ↦ (1 - (4 - σ²)α²)₊` to be integrable on the product
`(0, ∞) × (-1, 1]`. It is continuous, and it vanishes off the bounded set
`(0, 1] × (-1, 1]`, which is what makes it integrable despite the unbounded
`α`-range. -/

/-- The integrand of the area integral, as a function of the pair. -/
noncomputable def posPart (p : ℝ × ℝ) : ℝ :=
  max (1 - (4 - p.2 ^ 2) * p.1 ^ 2) 0

/-- The integrand is continuous on the product: a polynomial composed with
`max`. -/
theorem posPart_continuous : Continuous posPart := by
  unfold posPart
  exact (continuous_const.sub
    ((continuous_const.sub (continuous_snd.pow 2)).mul (continuous_fst.pow 2))).max
      continuous_const

/-- The integrand is nonnegative: it is a positive part. -/
theorem posPart_nonneg (p : ℝ × ℝ) : 0 ≤ posPart p := le_max_right _ _

/-- The integrand vanishes once `α > 1`: with `|σ| ≤ 1` one has `4 - σ² ≥ 3`, so
`(4 - σ²)α² > 3 > 1`. -/
theorem posPart_eq_zero_of_one_lt {p : ℝ × ℝ} (hp : |p.2| ≤ 1) (h1 : 1 < p.1) :
    posPart p = 0 := by
  have hsq : p.2 ^ 2 ≤ 1 := by nlinarith [abs_le.mp hp]
  have hone : (1 : ℝ) < p.1 ^ 2 := by nlinarith
  exact max_eq_right (by nlinarith)

/-- The integrand is integrable on `(0, ∞) × (-1, 1]`.

The set is unbounded, but by `posPart_eq_zero_of_one_lt` the integrand vanishes
outside `(0, 1] × (-1, 1]`, and on that bounded set it is the restriction of a
continuous function to a subset of a compact one. -/
theorem posPart_integrableOn :
    IntegrableOn posPart (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (-1 : ℝ) 1) (volume.prod volume) := by
  have hsub : Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (-1 : ℝ) 1
      ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (-1 : ℝ) 1 :=
    Set.prod_mono Set.Ioc_subset_Ioi_self (subset_refl _)
  rw [← Set.union_sdiff_cancel hsub, integrableOn_union]
  refine ⟨?_, ?_⟩
  · refine (posPart_continuous.continuousOn.integrableOn_compact
      (K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
      (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  · refine integrableOn_zero.congr_fun (fun p hp => ?_)
      ((measurableSet_Ioi.prod measurableSet_Ioc).diff
        (measurableSet_Ioc.prod measurableSet_Ioc))
    obtain ⟨⟨h0, hσ⟩, hnot⟩ := hp
    have h1 : 1 < p.1 := by
      by_contra h
      exact hnot ⟨⟨h0, not_lt.mp h⟩, hσ⟩
    exact (posPart_eq_zero_of_one_lt (abs_le.mpr ⟨hσ.1.le, hσ.2⟩) h1).symm

/-- `posPart_integrableOn` phrased for the product of the two restricted
measures, which is the form `MeasureTheory.integral_integral_swap` takes. -/
theorem posPart_integrable :
    Integrable posPart
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact posPart_integrableOn

/-- **The exchange of integration order.** -/
theorem integral_posPart_swap :
    (∫ α in Set.Ioi (0 : ℝ), ∫ σ in Set.Ioc (-1 : ℝ) 1, posPart (α, σ))
      = ∫ σ in Set.Ioc (-1 : ℝ) 1, ∫ α in Set.Ioi (0 : ℝ), posPart (α, σ) :=
  integral_integral_swap posPart_integrable

/-! ### The inner integral after the exchange -/

/-- **The inner `α`-integral.** For `c > 0`,

`∫_0^∞ (1 - c α²)_+ dα = (2/3) c^{-1/2}`.

The integrand is positive exactly on `[0, c^{-1/2})`, so the improper integral
is the integral of the polynomial `1 - c α²` over `(0, c^{-1/2}]`, which
`inner_integral` evaluates — the hypothesis `c A² = 1` holding for
`A = c^{-1/2}`. -/
theorem integral_max_one_sub_const_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ α in Set.Ioi (0 : ℝ), max (1 - c * α ^ 2) 0) = 2 / 3 * (1 / Real.sqrt c) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hA : (0 : ℝ) < 1 / Real.sqrt c := by positivity
  have hcA : c * (1 / Real.sqrt c) ^ 2 = 1 := by
    rw [div_pow, one_pow, Real.sq_sqrt hc.le]
    field_simp
  have hzero : ∀ α ∈ Set.Ioi (1 / Real.sqrt c), max (1 - c * α ^ 2) 0 = 0 := by
    intro α hα
    have hαA : 1 / Real.sqrt c < α := hα
    have hsum : (0 : ℝ) < α + 1 / Real.sqrt c := by linarith
    have hkey : 0 < c * ((α - 1 / Real.sqrt c) * (α + 1 / Real.sqrt c)) :=
      mul_pos hc (mul_pos (sub_pos.mpr hαA) hsum)
    exact max_eq_right (by nlinarith)
  rw [← Set.Ioc_union_Ioi_eq_Ioi hA.le,
    integral_union_eq_left_of_forall measurableSet_Ioi hzero]
  have hcongr : (∫ α in Set.Ioc (0 : ℝ) (1 / Real.sqrt c), max (1 - c * α ^ 2) 0)
      = ∫ α in Set.Ioc (0 : ℝ) (1 / Real.sqrt c), (1 - c * α ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro α hα
    obtain ⟨hα0, hαA⟩ := hα
    have hsum : (0 : ℝ) < α + 1 / Real.sqrt c := by linarith
    have hkey : 0 ≤ c * ((1 / Real.sqrt c - α) * (α + 1 / Real.sqrt c)) :=
      mul_nonneg hc.le (mul_nonneg (by linarith) hsum.le)
    exact max_eq_left (by nlinarith)
  rw [hcongr, ← intervalIntegral.integral_of_le hA.le, inner_integral hcA]
  ring

/-- **The pure number.** The double integral left by the two substitutions is

`∫_0^∞ ∫_{-1}^{1} (1 - (4 - σ²)α²)_+ dσ dα = (2/3)(π/3)`.

Exchange the order, evaluate the inner `α`-integral by
`integral_max_one_sub_const_mul_sq` with `c = 4 - σ² ≥ 3`, and evaluate the
resulting `σ`-integral of `(4 - σ²)^{-1/2}` by `arcsin_integral`. -/
theorem integral_posPart_double :
    (∫ α in Set.Ioi (0 : ℝ), ∫ σ in Set.Ioc (-1 : ℝ) 1, posPart (α, σ))
      = 2 / 3 * (π / 3) := by
  rw [integral_posPart_swap]
  have hinner : ∀ σ ∈ Set.Ioc (-1 : ℝ) 1,
      (∫ α in Set.Ioi (0 : ℝ), posPart (α, σ)) = 2 / 3 * (1 / Real.sqrt (4 - σ ^ 2)) := by
    intro σ hσ
    have habs : |σ| ≤ 1 := abs_le.mpr ⟨hσ.1.le, hσ.2⟩
    have hsq : σ ^ 2 ≤ 1 := by nlinarith [abs_le.mp habs]
    have hc : (0 : ℝ) < 4 - σ ^ 2 := by linarith
    simpa [posPart] using integral_max_one_sub_const_mul_sq hc
  rw [setIntegral_congr_fun measurableSet_Ioc hinner, MeasureTheory.integral_const_mul,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), arcsin_integral]

/-- **The area integral.** For `Y > 0`,

`∫_0^∞ F_Y(a) da = β Y^{3/2}`, where `β = π/108`.

The substitution `a = √Y α` turns the improper integral into
`√Y ∫_0^∞ F_Y(√Y α) dα`; `areaF_scaled_setIntegral` replaces the integrand by
`(Y/24) ∫_{-1}^{1} (1 - (4 - σ²)α²)_+ dσ`; and `integral_posPart_double`
evaluates the remaining pure number as `(2/3)(π/3)`. The constant closes exactly
against `beta_eq`, `β = (1/24)(2/3)(π/3)`.

`Y ^ (3/2)` is written `Y * sqrt Y`, which agrees with it for `Y ≥ 0`. -/
@[pz_tag "lem_F_integral"]
theorem integral_areaF {Y : ℝ} (hY : 0 < Y) :
    (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = beta * (Y * Real.sqrt Y) := by
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hscale : (∫ α in Set.Ioi (0 : ℝ), areaF Y (Real.sqrt Y * α))
      = (Real.sqrt Y)⁻¹ • ∫ a in Set.Ioi (Real.sqrt Y * 0), areaF Y a :=
    integral_comp_mul_left_Ioi (areaF Y) 0 hsY
  rw [mul_zero, smul_eq_mul] at hscale
  have hcongr : ∀ α ∈ Set.Ioi (0 : ℝ), areaF Y (Real.sqrt Y * α)
      = Y / 24 * ∫ σ in Set.Ioc (-1 : ℝ) 1, posPart (α, σ) := by
    intro α hα
    simpa [posPart] using areaF_scaled_setIntegral hY hα
  have hval : (∫ α in Set.Ioi (0 : ℝ), areaF Y (Real.sqrt Y * α))
      = Y / 24 * (2 / 3 * (π / 3)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
      integral_posPart_double]
  have hI : (∫ a in Set.Ioi (0 : ℝ), areaF Y a)
      = Real.sqrt Y * (Y / 24 * (2 / 3 * (π / 3))) := by
    rw [← hval, hscale, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsY), one_mul]
  rw [hI, beta_eq]
  ring

/-- **The integral of `L⁺` against `areaF`.** For `a > 0`,
`∫_{-a}^{a} L⁺(t) dt = 6 · F_Y(a)`.

`L⁺(t) = (Y + t² - 4a²)₊ / (4a)` and `F_Y(a) = (1/(24a)) ∫_{-a}^{a} (…)₊`, so the
two differ exactly by the factor `24a / 4a = 6`. -/
theorem integral_Lplus_eq {Y a : ℝ} (ha : 0 < a) :
    (∫ t in (-a)..a, Lplus Y a t) = 6 * areaF Y a := by
  have hane : a ≠ 0 := ne_of_gt ha
  unfold Lplus areaF
  rw [intervalIntegral.integral_div]
  field_simp
  ring

end PartitionZheng
