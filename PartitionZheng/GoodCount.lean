/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.BadCount

/-!
# Many good discriminants

The good discriminants are what is left of `admissible Y` after the bad ones are
removed, so their number is at least `#D(Y)` minus the number of bad ones. The
count of admissible discriminants supplies `#D(Y) ≥ delta * Y - C * sqrt Y` and
`bad_count` supplies `#bad(Y,H) ≤ (beta / H + ε / 2) * Y`; the error term
`C * sqrt Y` is absorbed into `(ε / 2) * Y` once `Y ≥ (2C/ε)²`.

## Main results

* `PartitionZheng.sqrt_error_le` — `C * sqrt Y ≤ (ε / 2) * Y` once
  `Y ≥ (2C/ε)²`.
* `PartitionZheng.good_count` — `#good(Y,H) ≥ (delta - beta / H - ε) Y` for `Y`
  large.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- A square-root error term is eventually below a linear one: `C * sqrt Y` is at
most `(ε / 2) * Y` as soon as `Y ≥ (2C/ε)²`. -/
theorem sqrt_error_le {C ε Y : ℝ} (hε : 0 < ε) (hY : (2 * C / ε) ^ 2 ≤ Y) :
    C * Real.sqrt Y ≤ ε / 2 * Y := by
  have hY0 : (0 : ℝ) ≤ Y := le_trans (sq_nonneg _) hY
  have hss : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0
  rcases le_or_gt C 0 with hC | hC
  · have h1 : C * Real.sqrt Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.sqrt_nonneg Y)
    have h2 : (0 : ℝ) ≤ ε / 2 * Y := by positivity
    linarith
  · have h1 : 2 * C / ε ≤ Real.sqrt Y := by
      rw [show 2 * C / ε = Real.sqrt ((2 * C / ε) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hY
    rw [div_le_iff₀ hε] at h1
    nlinarith [Real.sqrt_nonneg Y]

/-- **`lem_good_count`.** For every `ε > 0` the number of good discriminants up
to `Y` is at least `(delta - beta / H - ε) * Y`, once `Y` is large.

The hypothesis `hDset` asserts the count of admissible discriminants,
`|#D(Y) - delta * Y| ≤ C * sqrt Y` for some `C > 0`, and `hclass` asserts the
class-number average, `∑_{D ∈ D(Y)} h(D) ≤ (beta + ε) Y ^ (3/2)` for every
`ε > 0` once `Y` is large. -/
@[pz_tag "lem_good_count"]
theorem good_count {H : ℝ} (hH : 0 < H)
    (hDset : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      (delta - beta / H - ε) * Y ≤ ((good Y H).card : ℝ) := by
  obtain ⟨C, _, hDcard⟩ := hDset
  obtain ⟨Y₁, hY₁, hbad⟩ := bad_count hH hclass (half_pos hε)
  refine ⟨max Y₁ (max 2 ((2 * C / ε) ^ 2)), ?_, fun Y hY => ?_⟩
  · exact le_trans (le_max_left 2 _) (le_max_right Y₁ _)
  · have hY1' : Y₁ ≤ Y := le_trans (le_max_left _ _) hY
    have hY2 : (2 : ℝ) ≤ Y := le_trans (le_trans (le_max_left 2 _) (le_max_right Y₁ _)) hY
    have hYsq : (2 * C / ε) ^ 2 ≤ Y :=
      le_trans (le_trans (le_max_right 2 _) (le_max_right Y₁ _)) hY
    have hadm : delta * Y - C * Real.sqrt Y ≤ ((admissible Y).card : ℝ) := by
      have h := abs_le.mp (hDcard Y (by linarith))
      linarith [h.1]
    have hb := hbad Y hY1'
    have hsplit : ((admissible Y).card : ℝ)
        ≤ ((good Y H).card : ℝ) + ((bad Y H).card : ℝ) := by
      have h := card_admissible_le_card_good_add_card_bad (Y := Y) (H := H)
      exact_mod_cast h
    have herr : C * Real.sqrt Y ≤ ε / 2 * Y := sqrt_error_le hε hYsq
    have hexp : (beta / H + ε / 2) * Y = beta / H * Y + ε / 2 * Y := by ring
    rw [hexp] at hb
    have hgoal : (delta - beta / H - ε) * Y
        = delta * Y - beta / H * Y - ε / 2 * Y - ε / 2 * Y := by ring
    rw [hgoal]
    linarith

end PartitionZheng
