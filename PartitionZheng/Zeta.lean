/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import PartitionZheng.Meta.Attr

/-!
# The Basel sum

`zeta 2 = pi ^ 2 / 6` is what turns the Euler product
`prod_{p >= 5} (1 - p⁻²)` into `9 / pi ^ 2`, and hence what puts the `pi` into
the density constant `delta = 3 / (8 pi ^ 2)`.

It is a theorem here rather than an assumption: Mathlib proves it.

Note the sum runs over all of `ℕ`, including `0`, where the summand is `1 / 0`;
Lean's convention makes that `0`, so the sum agrees with the usual sum over
`k ≥ 1`.

## Main results

* `PartitionZheng.basel` — `∑' n, 1 / n ^ 2 = pi ^ 2 / 6`.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- The Basel sum, from Mathlib's `hasSum_zeta_two`. -/
@[pz_tag "thm_basel"]
theorem basel : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

end PartitionZheng
