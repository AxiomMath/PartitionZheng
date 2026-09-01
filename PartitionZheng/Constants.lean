/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PartitionZheng.Meta.Attr

/-!
# The two constants of Zheng's argument

`delta` is the density of admissible discriminants among the integers, and
`beta` bounds their average class number. The final constant
`243 / (64 * sqrt 6 * pi ^ 5)` is `delta ^ 2 / (4 * beta * sqrt 6)`.

## Main definitions

* `PartitionZheng.delta` — the density constant `3 / (8 * pi ^ 2)`.
* `PartitionZheng.beta` — the class-number constant `pi / 108`.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- The density of the admissible discriminants: `#D(Y) = delta * Y + O(sqrt Y)`. -/
@[pz_tag "def_delta"]
noncomputable def delta : ℝ := 3 / (8 * π ^ 2)

/-- The constant bounding the average class number:
`sum_{D in D(Y)} h(D) <= (beta + o(1)) * Y ^ (3/2)`. -/
@[pz_tag "def_beta"]
noncomputable def beta : ℝ := π / 108

/-- The density constant `delta` is positive. -/
lemma delta_pos : 0 < delta := by
  unfold delta; positivity

/-- The density factors as `δ = (1/24) · (9/π²)`.

The two factors are the density `1/24` of one residue class modulo `24` and the
series `∑_{(d,6)=1} μ(d)/d² = 9/π²` of `coprime_moebius_tsum`, the count of the
admissible discriminants up to `Y` being `(Y/24) · ∑_{(d,6)=1} μ(d)/d² + O(√Y)`. -/
theorem delta_eq : delta = (1 / 24) * (9 / π ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold delta
  field_simp
  ring

/-- The class-number constant factors as `β = (1/24) · (2/3) · (π/3)`.

The three factors are the prefactor `1/24` left by the two substitutions of the
area integral, the value `(2/3)(4-σ²)^{-1/2}` of the inner `α`-integral given by
`inner_integral`, and the value `π/3` of the resulting `σ`-integral given by
`arcsin_integral`. Their product is `(1/24)(2/3)(π/3) = 2π/216 = π/108`. -/
theorem beta_eq : beta = (1 / 24) * ((2 / 3) * (π / 3)) := by
  unfold beta
  ring

/-- The class-number constant `beta` is positive. -/
lemma beta_pos : 0 < beta := by
  unfold beta; positivity

end PartitionZheng
