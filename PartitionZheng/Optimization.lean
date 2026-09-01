/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import PartitionZheng.Constants

/-!
# The optimal threshold and the constant

The lower bound of the argument is `(delta - beta / H) / (sqrt 6 * H)` for any
threshold `H > beta / delta`. This file maximises it. The maximum is at
`H = 2 * beta / delta`, where the value is `delta ^ 2 / (4 * beta * sqrt 6)`,
and that equals `243 / (64 * sqrt 6 * pi ^ 5)`.

The `sqrt 6` is a constant factor common to both sides, so every statement here
is phrased with it divided out: `H_admissible` and `optimal_value` are about
`(delta - beta / H) / H`, and `constant_value` about
`delta ^ 2 / (4 * beta)`. Reinstating the factor is a single division, done
where the limit inferior is assembled. This keeps the arithmetic exact and this
module's imports small.

## Main results

* `PartitionZheng.H_admissible` — the optimal threshold is admissible.
* `PartitionZheng.optimal_value` — the value there, `delta ^ 2 / (4 * beta)`.
* `PartitionZheng.constant_value` — that equals `243 / (64 * pi ^ 5)`.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- At the optimal threshold `H = 2 * beta / delta` the numerator
`delta - beta / H` equals `delta / 2`, which is positive; so the threshold is
admissible, i.e. it exceeds `beta / delta`. -/
@[pz_tag "lem_H_admissible"]
theorem H_admissible : 0 < delta - beta / (2 * beta / delta) := by
  have hb : beta ≠ 0 := ne_of_gt beta_pos
  have hd : delta ≠ 0 := ne_of_gt delta_pos
  have key : beta / (2 * beta / delta) = delta / 2 := by
    field_simp
  rw [key]
  have := delta_pos
  linarith

/-- The value at the optimal threshold, with the common `sqrt 6` divided out. -/
@[pz_tag "lem_optimal_value"]
theorem optimal_value :
    (delta - beta / (2 * beta / delta)) / (2 * beta / delta)
      = delta ^ 2 / (4 * beta) := by
  have hb : beta ≠ 0 := ne_of_gt beta_pos
  have hd : delta ≠ 0 := ne_of_gt delta_pos
  field_simp
  ring

/-- The constant: `delta ^ 2 / (4 * beta) = 243 / (64 * pi ^ 5)`. With the
`sqrt 6` reinstated this is the corollary's `243 / (64 * sqrt 6 * pi ^ 5)`. -/
@[pz_tag "lem_constant"]
theorem constant_value : delta ^ 2 / (4 * beta) = 243 / (64 * π ^ 5) := by
  have hpi : π ≠ 0 := ne_of_gt pi_pos
  unfold delta beta
  field_simp
  ring

end PartitionZheng
