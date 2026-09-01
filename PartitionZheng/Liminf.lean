/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.Asymptotic
public import PartitionZheng.Counting
public import PartitionZheng.GoodCount
public import PartitionZheng.LiminfEReal

/-!
# The lower bound at a fixed threshold

For a threshold `H` with `delta - beta / H > 0` the argument closes. Write
`A = delta - beta / H` and `K = 1 / (sqrt 6 * H)`. At `X = Z_H(Y_X)` the counting
step gives `N_odd(X) ≥ #good(Y_X, H)`, the count of good discriminants gives
`#good(Y_X, H) ≥ (A - ε₁) Y_X`, and the change of variable gives
`Y_X / sqrt X ≥ K - ε₂`. Multiplying,

`N_odd(X) / sqrt X ≥ (A - ε₁)(K - ε₂) ≥ A * K - ε`

once `ε₁ * K ≤ ε / 2` and `A * ε₂ ≤ ε / 2`, which is what the choices
`ε₁ = min A (ε / (2K))` and `ε₂ = min K (ε / (2A))` arrange; the two minima also
keep both factors nonnegative, which is what lets the product be bounded.

The two counting inputs enter as explicit hypotheses: `hDset` says the number of
admissible discriminants up to `Y` is `delta * Y` up to an error `O(sqrt Y)`, and
`hclass` that for every `ε > 0` the class numbers of those discriminants sum to
at most `(beta + ε) * Y * sqrt Y` once `Y` is large. `hp` is the parity theorem
`ParityInput`.

## Main results

* `PartitionZheng.Nodd_eventually_ge` — the explicit quantified form.
* `PartitionZheng.liminf_Nodd_ge` — the limit inferior at a fixed threshold.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- At `X = Z_H(Y_X)`, `N_odd(X)` is at least the number of good discriminants
up to `Y_X`. -/
theorem card_good_le_Nodd (hp : ParityInput) {H X : ℝ} (hH : 0 < H)
    (hX : ZH H 0 ≤ X) : ((good (YX H X) H).card : ℝ) ≤ (Nodd ⌊X⌋₊ : ℝ) := by
  obtain ⟨hY0, heq⟩ := YX_spec hH hX
  have h := Nodd_lower hp (Y := YX H X) (H := H) hY0
  rw [heq] at h
  exact_mod_cast h

/-- For a threshold `H` with `delta - beta / H > 0` and every `ε > 0`, the ratio
`N_odd(X) / sqrt X` is eventually at least `(delta - beta / H) / (sqrt 6 * H) - ε`. -/
theorem Nodd_eventually_ge (hp : ParityInput) {H : ℝ} (hH : 0 < H)
    (hadm : 0 < delta - beta / H)
    (hDset : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop,
      (delta - beta / H) / (Real.sqrt 6 * H) - ε ≤ (Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X := by
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (0 : ℝ) < Real.sqrt 6 * H := mul_pos h6 hH
  set A : ℝ := delta - beta / H with hAdef
  set K : ℝ := 1 / (Real.sqrt 6 * H) with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  -- the two slacks, chosen so that `ε₁ * K` and `A * ε₂` are each at most `ε / 2`
  set ε₁ : ℝ := min A (ε / (2 * K)) with hε₁def
  set ε₂ : ℝ := min K (ε / (2 * A)) with hε₂def
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; exact lt_min hadm (by positivity)
  have hε₂ : 0 < ε₂ := by rw [hε₂def]; exact lt_min hK (by positivity)
  have hA1 : 0 ≤ A - ε₁ := by
    have : ε₁ ≤ A := by rw [hε₁def]; exact min_le_left _ _
    linarith
  have hε₁K : ε₁ * K ≤ ε / 2 := by
    have h1 : ε₁ ≤ ε / (2 * K) := by rw [hε₁def]; exact min_le_right _ _
    have h2 : ε / (2 * K) * K = ε / 2 := by field_simp
    calc ε₁ * K ≤ ε / (2 * K) * K := mul_le_mul_of_nonneg_right h1 hK.le
      _ = ε / 2 := h2
  have hAε₂ : A * ε₂ ≤ ε / 2 := by
    have h1 : ε₂ ≤ ε / (2 * A) := by rw [hε₂def]; exact min_le_right _ _
    have h2 : A * (ε / (2 * A)) = ε / 2 := by field_simp
    calc A * ε₂ ≤ A * (ε / (2 * A)) := mul_le_mul_of_nonneg_left h1 hadm.le
      _ = ε / 2 := h2
  have hprod : A * K - ε ≤ (A - ε₁) * (K - ε₂) := by
    nlinarith [mul_pos hε₁ hε₂]
  obtain ⟨Y₀, hY₀, hgood⟩ := good_count hH hDset hclass hε₁
  have hlim := YX_asymptotic hH
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨X₁, hX₁⟩ := hlim ε₂ hε₂
  refine Filter.eventually_atTop.mpr ⟨max (max X₁ (ZH H Y₀)) 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
  have hZ0 : ZH H 0 ≤ X := by
    have hz : ZH H 0 = 1 / 24 := by unfold ZH; norm_num
    rw [hz]; linarith
  have hXY₀ : ZH H Y₀ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hYbig : Y₀ ≤ YX H X := le_YX hH (by linarith) hXY₀
  -- `N_odd(X) ≥ #good(Y_X, H) ≥ (A - ε₁) Y_X`
  have hNodd : (A - ε₁) * YX H X ≤ (Nodd ⌊X⌋₊ : ℝ) :=
    le_trans (hgood (YX H X) hYbig) (card_good_le_Nodd hp hH hZ0)
  -- `Y_X / sqrt X ≥ K - ε₂`
  have hratio : (K - ε₂) * Real.sqrt X ≤ YX H X := by
    have h := hX₁ X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
    rw [Real.dist_eq, abs_lt] at h
    have h1 : K - ε₂ ≤ YX H X / Real.sqrt X := by
      rw [hKdef]; linarith [h.1]
    rw [← le_div_iff₀ hsX]
    exact h1
  have hAK : A / (Real.sqrt 6 * H) = A * K := by rw [hKdef, mul_one_div]
  rw [le_div_iff₀ hsX, hAK]
  have hstep1 : (A * K - ε) * Real.sqrt X ≤ (A - ε₁) * (K - ε₂) * Real.sqrt X :=
    mul_le_mul_of_nonneg_right hprod hsX.le
  have hstep2 : (A - ε₁) * (K - ε₂) * Real.sqrt X ≤ (A - ε₁) * YX H X := by
    calc (A - ε₁) * (K - ε₂) * Real.sqrt X = (A - ε₁) * ((K - ε₂) * Real.sqrt X) := by ring
      _ ≤ (A - ε₁) * YX H X := mul_le_mul_of_nonneg_left hratio hA1
  linarith

/-- **`lem_liminf_H`.** For a threshold `H` with `delta - beta / H > 0`,

`liminf_{X → ∞} N_odd(X) / sqrt X ≥ (delta - beta / H) / (sqrt 6 * H)`.

The limit inferior is formed in `EReal`; see `le_liminf_of_eventually_sub_le` for
why the real-valued one would be junk. -/
@[pz_tag "lem_liminf_H"]
theorem liminf_Nodd_ge (hp : ParityInput) {H : ℝ} (hH : 0 < H)
    (hadm : 0 < delta - beta / H)
    (hDset : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y)) :
    (((delta - beta / H) / (Real.sqrt 6 * H) : ℝ) : EReal) ≤
      Filter.liminf (fun X : ℝ => (((Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X : ℝ) : EReal))
        Filter.atTop :=
  le_liminf_of_eventually_sub_le fun _ hδ => Nodd_eventually_ge hp hH hadm hDset hclass hδ

end PartitionZheng
