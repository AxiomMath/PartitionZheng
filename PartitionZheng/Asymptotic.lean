/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.Range

/-!
# The change of variable

`YX H X` is the unique `Y ≥ 0` with `Z_H Y = X`. This file names it and proves
the asymptotic `Y_X / sqrt X → 1 / (sqrt 6 * H)`.

Since `Z_H Y = 6 H² Y² + 2 H Y^{3/2} + Y/6 + 1/24` has nonnegative lower-order
terms, `6 H² Y² ≤ X` outright, giving the exact upper bound
`Y ≤ sqrt X / (sqrt 6 H)`. In the other direction the tail is eventually at
most `δ` times the quadratic term, so `X ≤ (1 + δ) 6 H² Y²` and
`Y ≥ sqrt X / (sqrt 6 H sqrt (1 + δ))`. The two bounds squeeze the ratio, and
`1 - 1/sqrt (1 + d) ≤ d` turns the squeeze into an explicit modulus, avoiding
any continuity argument for `d ↦ 1/sqrt (1 + d)` at `0`.

## Main definitions

* `PartitionZheng.YX` — the solution of `Z_H Y = X`.

## Main results

* `PartitionZheng.YX_le_sqrt` — the exact upper bound.
* `PartitionZheng.sqrt_le_YX` — the lower bound for each fixed `δ > 0`.
* `PartitionZheng.YX_asymptotic` — the asymptotic.
-/

@[expose] public section

namespace PartitionZheng

open Real

open Classical in
/-- The solution of `Z_H Y = X` with `Y ≥ 0`, junk value `0` when there is
none. `lem_YX_exists` shows it exists and is unique for `X ≥ Z_H 0`. -/
noncomputable def YX (H X : ℝ) : ℝ :=
  if h : ∃ Y, 0 ≤ Y ∧ ZH H Y = X then h.choose else 0

/-- `YX` solves the equation, when a solution exists. -/
theorem YX_spec {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    0 ≤ YX H X ∧ ZH H (YX H X) = X := by
  classical
  have hex : ∃ Y, 0 ≤ Y ∧ ZH H Y = X := (exists_unique_YX hH hX).exists
  rw [YX, dite_eq_left hex]
  exact hex.choose_spec

/-- The three lower-order terms of `Z_H` are nonnegative at `YX H X`. -/
theorem YX_tail_nonneg {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    0 ≤ 2 * H * (YX H X * Real.sqrt (YX H X)) + YX H X / 6 + 1 / 24 := by
  obtain ⟨hY0, _⟩ := YX_spec hH hX
  have hs : 0 ≤ Real.sqrt (YX H X) := Real.sqrt_nonneg _
  have h1 : 0 ≤ YX H X * Real.sqrt (YX H X) := mul_nonneg hY0 hs
  have h2 : 0 ≤ 2 * H * (YX H X * Real.sqrt (YX H X)) := by positivity
  linarith

/-- `X` minus the lower-order tail is at most the quadratic term. A restatement
of `Z_H (YX H X) = X`, recorded because the limit argument starts here. -/
theorem YX_quadratic_lower {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    X - (2 * H * (YX H X * Real.sqrt (YX H X)) + YX H X / 6 + 1 / 24)
      ≤ 6 * H ^ 2 * (YX H X) ^ 2 := by
  obtain ⟨_, heq⟩ := YX_spec hH hX
  -- Unfold in the hypothesis; rewriting `X` in the goal would also rewrite the
  -- `X` inside `YX H X` and blow it up.
  unfold ZH at heq
  linarith

/-- `6 H² Y² ≤ X`: the quadratic term alone cannot exceed `X`, since the other
three terms of `Z_H` are nonnegative. -/
theorem quad_le {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    6 * H ^ 2 * (YX H X) ^ 2 ≤ X := by
  obtain ⟨hY0, heq⟩ := YX_spec hH hX
  have htail := YX_tail_nonneg hH hX
  -- Unfold in the HYPOTHESIS: rewriting `X` would also rewrite it inside
  -- `YX H X` and blow the goal up.
  unfold ZH at heq
  linarith

/-- Hence the exact upper bound `Y ≤ sqrt X / (sqrt 6 * H)`. -/
theorem YX_le_sqrt {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    YX H X ≤ Real.sqrt X / (Real.sqrt 6 * H) := by
  obtain ⟨hY0, _⟩ := YX_spec hH hX
  have hq := quad_le hH hX
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (0 : ℝ) < Real.sqrt 6 * H := mul_pos h6 hH
  rw [le_div_iff₀ hden]
  -- `(Y * (√6 * H))² = 6 H² Y² ≤ X = (√X)²`, and both sides are nonneg.
  have hX0 : (0 : ℝ) ≤ X := le_trans (by positivity) hq
  have hsq6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsqX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
  nlinarith [Real.sqrt_nonneg X, mul_nonneg hY0 (le_of_lt hden)]

/-- `YX H X` is at least `M` as soon as `X` is at least `Z_H M`: strict
monotonicity of `Z_H` inverts the inequality. -/
theorem le_YX {H X M : ℝ} (hH : 0 < H) (hM : 0 ≤ M) (hX : ZH H M ≤ X) :
    M ≤ YX H X := by
  have hmono := ZH_strictMonoOn hH
  have h0M : ZH H 0 ≤ ZH H M := by
    rcases eq_or_lt_of_le hM with h | h
    · subst h; exact le_refl _
    · exact le_of_lt (hmono Set.self_mem_Ici (Set.mem_Ici.mpr hM) h)
  have hX0 : ZH H 0 ≤ X := le_trans h0M hX
  obtain ⟨hY0, heq⟩ := YX_spec hH hX0
  by_contra hc
  have hlt : YX H X < M := by linarith [not_le.mp hc]
  have := hmono (Set.mem_Ici.mpr hY0) (Set.mem_Ici.mpr hM) hlt
  rw [heq] at this
  linarith

/-- For `Y` large, the three lower-order terms of `Z_H` are at most `δ` times
the quadratic term. Concretely, for `Y ≥ 1` they are all at most a constant
times `Y * sqrt Y`, and `Y * sqrt Y / Y² = 1 / sqrt Y → 0`. -/
theorem tail_le_of_large {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y, Y₀ ≤ Y →
      2 * H * (Y * Real.sqrt Y) + Y / 6 + 1 / 24 ≤ δ * (6 * H ^ 2 * Y ^ 2) := by
  set C : ℝ := 2 * H + 5 / 24 with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  refine ⟨max 1 ((C / (6 * H ^ 2 * δ)) ^ 2 + 1), le_max_left _ _, ?_⟩
  intro Y hY
  have hY1 : (1 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hs : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0
  have hs1 : (1 : ℝ) ≤ Real.sqrt Y := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hY1
  -- each lower-order term is at most `Y * sqrt Y`
  have hle1 : Y ≤ Y * Real.sqrt Y := by nlinarith
  have hle2 : (1 : ℝ) ≤ Y * Real.sqrt Y := by nlinarith
  have hsum : 2 * H * (Y * Real.sqrt Y) + Y / 6 + 1 / 24 ≤ C * (Y * Real.sqrt Y) := by
    rw [hC]; nlinarith
  -- and `C * Y * sqrt Y ≤ δ * 6 H² Y²` once `sqrt Y ≥ C / (6 H² δ)`
  have hbig : C / (6 * H ^ 2 * δ) ≤ Real.sqrt Y := by
    have hsq : (C / (6 * H ^ 2 * δ)) ^ 2 ≤ Y := by
      have := le_trans (le_max_right 1 ((C / (6 * H ^ 2 * δ)) ^ 2 + 1)) hY
      linarith
    have hnn : 0 ≤ C / (6 * H ^ 2 * δ) := by positivity
    nlinarith [Real.sqrt_nonneg Y]
  have hden : (0 : ℝ) < 6 * H ^ 2 * δ := by positivity
  have hstep : C * (Y * Real.sqrt Y) ≤ δ * (6 * H ^ 2 * Y ^ 2) := by
    rw [div_le_iff₀ hden] at hbig
    have hmul := mul_le_mul_of_nonneg_right hbig (mul_nonneg hY0 (Real.sqrt_nonneg Y))
    calc C * (Y * Real.sqrt Y)
        ≤ Real.sqrt Y * (6 * H ^ 2 * δ) * (Y * Real.sqrt Y) := hmul
      _ = 6 * H ^ 2 * δ * Y * Real.sqrt Y ^ 2 := by ring
      _ = δ * (6 * H ^ 2 * Y ^ 2) := by rw [hs]; ring
  linarith

/-- The lower half of the asymptotic: once `X` is large, `Y` is at least
`sqrt X / (sqrt 6 * H * sqrt (1 + δ))`. From `X ≤ (1 + δ) * 6 H² Y²`. -/
theorem sqrt_le_YX {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) :
    ∃ X₀ : ℝ, ∀ X, X₀ ≤ X →
      Real.sqrt X / (Real.sqrt 6 * H * Real.sqrt (1 + δ)) ≤ YX H X := by
  obtain ⟨Y₀, hY₀1, hY₀⟩ := tail_le_of_large hH hδ
  refine ⟨max (ZH H Y₀) (ZH H 0), ?_⟩
  intro X hX
  have hX0 : ZH H 0 ≤ X := le_trans (le_max_right _ _) hX
  have hXY₀ : ZH H Y₀ ≤ X := le_trans (le_max_left _ _) hX
  obtain ⟨hY0, heq⟩ := YX_spec hH hX0
  have hYbig : Y₀ ≤ YX H X := le_YX hH (by linarith) hXY₀
  -- `X = Z_H Y ≤ (1 + δ) * 6 H² Y²`
  have hub : X ≤ (1 + δ) * (6 * H ^ 2 * (YX H X) ^ 2) := by
    have htail := hY₀ (YX H X) hYbig
    unfold ZH at heq
    linarith
  have hXnn : (0 : ℝ) ≤ X := le_trans (by positivity) (quad_le hH hX0)
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hd : (0 : ℝ) < Real.sqrt (1 + δ) := Real.sqrt_pos.mpr (by linarith)
  have hden : (0 : ℝ) < Real.sqrt 6 * H * Real.sqrt (1 + δ) := by positivity
  rw [div_le_iff₀ hden]
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsd : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
  have hk : (0 : ℝ) ≤ YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ)) :=
    mul_nonneg hY0 (le_of_lt hden)
  -- Square both sides explicitly; `nlinarith` will not find this on its own.
  have hsq : X ≤ (YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ))) ^ 2 := by
    have hexp : (YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ))) ^ 2
        = YX H X ^ 2 * Real.sqrt 6 ^ 2 * H ^ 2 * Real.sqrt (1 + δ) ^ 2 := by ring
    rw [hexp, hs6, hsd]
    linarith
  calc Real.sqrt X
      ≤ Real.sqrt ((YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ))) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ)) := Real.sqrt_sq hk

/-- `1 - 1/sqrt (1+d) ≤ d` for `0 ≤ d`: squaring, `(1-d)²(1+d) ≤ 1` reduces to
`d² ≤ 1 + d`. This is the explicit modulus that replaces a continuity argument
for `d ↦ 1/sqrt (1+d)` at `0`. -/
theorem one_sub_inv_sqrt_le {d : ℝ} (hd : 0 ≤ d) :
    1 - 1 / Real.sqrt (1 + d) ≤ d := by
  have h1 : (0 : ℝ) < 1 + d := by linarith
  have hs : (0 : ℝ) < Real.sqrt (1 + d) := Real.sqrt_pos.mpr h1
  have hsq : Real.sqrt (1 + d) ^ 2 = 1 + d := Real.sq_sqrt (le_of_lt h1)
  rcases le_or_gt 1 d with hge | hlt
  · have hle1 : 1 / Real.sqrt (1 + d) ≤ 1 := by
      rw [div_le_one hs]
      nlinarith [Real.sqrt_nonneg (1 + d)]
    have hnn : (0 : ℝ) ≤ 1 / Real.sqrt (1 + d) := by positivity
    linarith
  · -- `1 - d > 0`; show `(1 - d) * sqrt (1 + d) ≤ 1`, then divide
    have hkey : (1 - d) * Real.sqrt (1 + d) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (1 + d), hsq]
    have hstep : 1 - d ≤ 1 / Real.sqrt (1 + d) := by
      rw [le_div_iff₀ hs]; exact hkey
    linarith

/-- **The change of variable, asymptotically.** `Y_X / sqrt X → 1 / (sqrt 6 H)`.

`YX_le_sqrt` gives the exact upper bound, so the ratio never exceeds the limit.
`sqrt_le_YX` gives `1 / sqrt (1 + d)` of it for each `d > 0`, and
`one_sub_inv_sqrt_le` bounds the shortfall by `d` — so choosing `d` small
against `ε * sqrt 6 * H` closes the gap without any continuity argument. -/
@[pz_tag "lem_YX_asymp"]
theorem YX_asymptotic {H : ℝ} (hH : 0 < H) :
    Filter.Tendsto (fun X : ℝ => YX H X / Real.sqrt X) Filter.atTop
      (nhds (1 / (Real.sqrt 6 * H))) := by
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (0 : ℝ) < Real.sqrt 6 * H := mul_pos h6 hH
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- pick `d` so the shortfall `(1/(√6 H)) * d` is below `ε`
  set d : ℝ := min 1 (ε * (Real.sqrt 6 * H) / 2) with hdd
  have hd0 : 0 < d := by
    rw [hdd]; exact lt_min one_pos (by positivity)
  have hdle : d ≤ ε * (Real.sqrt 6 * H) / 2 := by rw [hdd]; exact min_le_right _ _
  obtain ⟨X₀, hX₀⟩ := sqrt_le_YX hH hd0
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hZ0 : ZH H 0 ≤ X := by
    have hz : ZH H 0 = 1 / 24 := by unfold ZH; norm_num
    rw [hz]; linarith
  have hsd : (0 : ℝ) < Real.sqrt (1 + d) := Real.sqrt_pos.mpr (by linarith)
  -- the two bounds on the ratio
  have hupp : YX H X / Real.sqrt X ≤ 1 / (Real.sqrt 6 * H) := by
    have h := YX_le_sqrt hH hZ0
    rw [le_div_iff₀ hden] at h
    rw [div_le_div_iff₀ hsX hden]
    linarith
  have hlow : 1 / (Real.sqrt 6 * H * Real.sqrt (1 + d)) ≤ YX H X / Real.sqrt X := by
    have h := hX₀ X (le_trans (le_max_left _ _) hX)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt 6 * H * Real.sqrt (1 + d))] at h
    rw [div_le_div_iff₀ (by positivity) hsX]
    linarith
  -- the shortfall is at most `(1/(√6 H)) * d ≤ ε/2 < ε`
  have hgap : 1 / (Real.sqrt 6 * H) - 1 / (Real.sqrt 6 * H * Real.sqrt (1 + d))
      ≤ 1 / (Real.sqrt 6 * H) * d := by
    have hfac : 1 / (Real.sqrt 6 * H * Real.sqrt (1 + d))
        = 1 / (Real.sqrt 6 * H) * (1 / Real.sqrt (1 + d)) := by
      field_simp
    rw [hfac]
    have := one_sub_inv_sqrt_le (le_of_lt hd0)
    have hpos : (0 : ℝ) < 1 / (Real.sqrt 6 * H) := by positivity
    nlinarith
  have hhalf : 1 / (Real.sqrt 6 * H) * d ≤ ε / 2 := by
    have hpos : (0 : ℝ) < 1 / (Real.sqrt 6 * H) := by positivity
    have : d ≤ ε * (Real.sqrt 6 * H) / 2 := hdle
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden] at *
    nlinarith
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

end PartitionZheng
