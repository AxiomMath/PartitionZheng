/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.LiminfLimsup

/-!
# Limits inferior of real functions, formed in `EReal`

The corollary bounds `liminf_{X → ∞} N_odd(X) / sqrt X` from below. That limit
inferior is taken in `EReal`, not in `ℝ`, and the reason is not cosmetic:
`Filter.liminf` is `sSup {a | ∀ᶠ X, a ≤ u X}`, and `Real.sSup` of a set
unbounded above is the junk value `0`. Nothing available bounds
`N_odd(X) / sqrt X` from above — the expected truth is that it tends to infinity,
which would make the set unbounded and the real-valued limit inferior equal to
`0`. In `EReal`, a complete lattice, the limit inferior always exists and agrees
with the classical one, so the inequality means what it says.

## Main results

* `PartitionZheng.le_liminf_of_eventually_sub_le` — an `ε`-`δ` lower bound gives
  a lower bound on the limit inferior.
-/

@[expose] public section

namespace PartitionZheng

/-- If for every `ε > 0` the function `u` is eventually at least `c - ε`, then
its limit inferior at infinity, formed in `EReal`, is at least `c`.

This is the passage from the explicit quantified form in which the argument
produces its estimates to the limit inferior the statement is about. -/
theorem le_liminf_of_eventually_sub_le {c : ℝ} {u : ℝ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ X in Filter.atTop, c - ε ≤ u X) :
    (c : EReal) ≤ Filter.liminf (fun X : ℝ => ((u X : ℝ) : EReal)) Filter.atTop := by
  have key : ∀ r : ℝ, r < c →
      ((r : ℝ) : EReal) ≤ Filter.liminf (fun X : ℝ => ((u X : ℝ) : EReal)) Filter.atTop := by
    intro r hr
    have hev : ∀ᶠ X in Filter.atTop, ((r : ℝ) : EReal) ≤ ((u X : ℝ) : EReal) := by
      filter_upwards [h (c - r) (by linarith)] with X hX
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    exact Filter.le_liminf_of_le (h := hev)
  refine le_of_forall_lt ?_
  intro z
  induction z using EReal.rec with
  | bot =>
      intro _
      exact lt_of_lt_of_le (EReal.bot_lt_coe (c - 1)) (key (c - 1) (by linarith))
  | coe r =>
      intro hz
      have hrc : r < c := EReal.coe_lt_coe_iff.mp hz
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith : r < (r + c) / 2))
        (key ((r + c) / 2) (by linarith))
  | top => intro hz; exact absurd hz not_top_lt

end PartitionZheng
