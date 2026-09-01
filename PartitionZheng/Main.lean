/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.Assemble
public import PartitionZheng.DsetCount
public import PartitionZheng.Liminf
public import PartitionZheng.Optimization

/-!
# Zheng's lower bound

The corollary of Qi-Yang Zheng: the number of `n ≤ X` with `p n` odd is at least
`(243 / (64 * sqrt 6 * pi ^ 5) + o(1)) * sqrt X`, in the sense that

`liminf_{X → ∞} N_odd(X) / sqrt X ≥ 243 / (64 * sqrt 6 * pi ^ 5)`.

The bound of `liminf_Nodd_ge` holds for every threshold `H` with
`delta - beta / H > 0`; this file takes `H = 2 * beta / delta`, admissible by
`H_admissible`, where `optimal_value` and `constant_value` identify the bound as
`delta ^ 2 / (4 * beta * sqrt 6) = 243 / (64 * sqrt 6 * pi ^ 5)`.

## Main results

* `PartitionZheng.liminf_Nodd_ge_const` — the corollary.
* `PartitionZheng.Nodd_eventually_ge_const` — its explicit quantified form.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- At the threshold `H = 2 * beta / delta`,
`(delta - beta / H) / (sqrt 6 * H) = 243 / (64 * sqrt 6 * pi ^ 5)`. -/
theorem optimal_bound_eq :
    (delta - beta / (2 * beta / delta)) / (Real.sqrt 6 * (2 * beta / delta))
      = 243 / (64 * Real.sqrt 6 * π ^ 5) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h6 : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h1 : (delta - beta / (2 * beta / delta)) / (Real.sqrt 6 * (2 * beta / delta))
      = (delta - beta / (2 * beta / delta)) / (2 * beta / delta) / Real.sqrt 6 := by
    rw [mul_comm (Real.sqrt 6) (2 * beta / delta), ← div_div]
  rw [h1, optimal_value, constant_value]
  field_simp

/-- The optimal threshold is positive. -/
theorem optimal_threshold_pos : 0 < 2 * beta / delta := by
  have hb := beta_pos
  have hd := delta_pos
  positivity

/-- **`thm_main`. Zheng's lower bound.**

`liminf_{X → ∞} N_odd(X) / sqrt X ≥ 243 / (64 * sqrt 6 * pi ^ 5)`,

the limit inferior being over real `X` and formed in `EReal` (see
`le_liminf_of_eventually_sub_le`: the real-valued limit inferior of an
expression with no available upper bound is the junk value `0`).

The hypothesis `hp` is the parity theorem `ParityInput`; the count of the
admissible discriminants and the average of their class numbers come from
`card_admissible_sub_delta_le` and `class_average_unconditional`. -/
@[pz_tag "thm_main"]
theorem liminf_Nodd_ge_const (hp : ParityInput) :
    ((243 / (64 * Real.sqrt 6 * π ^ 5) : ℝ) : EReal) ≤
      Filter.liminf (fun X : ℝ => (((Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X : ℝ) : EReal))
        Filter.atTop := by
  rw [← optimal_bound_eq]
  exact liminf_Nodd_ge hp optimal_threshold_pos H_admissible
    card_admissible_sub_delta_le class_average_unconditional

/-- For every `ε > 0` the ratio `N_odd(X) / sqrt X` is eventually at least
`243 / (64 * sqrt 6 * pi ^ 5) - ε`, with `hp` the parity theorem
`ParityInput`. -/
theorem Nodd_eventually_ge_const (hp : ParityInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop,
      243 / (64 * Real.sqrt 6 * π ^ 5) - ε ≤ (Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X := by
  rw [← optimal_bound_eq]
  exact Nodd_eventually_ge hp optimal_threshold_pos H_admissible
    card_admissible_sub_delta_le class_average_unconditional hε

end PartitionZheng
