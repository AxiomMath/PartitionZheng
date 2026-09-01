/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.Basic
public import PartitionZheng.Meta.Attr

/-!
# The residue weight

For a fixed first coefficient `a`, the discriminant congruence confines the
outer coefficient `c` to a union of residue classes modulo `6`: those with
`a * c ≡ 0` when `b` is coprime to `3`, and those with `a * c ≡ 2` when
`3 ∣ b`. Counting the first case twice — once for each of `b ≡ 1, 5 [MOD 6]` —
gives the weight `w a`.

It depends on `a` only through `a` modulo `6`, and takes the values
`12, 3, 6, 6, 6, 3`, so its mean over a period is `6`. That mean is what lets
partial summation replace `w a / 6` by `1` in the lattice count.

## Main definitions

* `PartitionZheng.weight` — the weight `w a`.

## Main results

* `PartitionZheng.weight_values` — the six values.
* `PartitionZheng.weight_sum` — they sum to `36`, hence mean `6`.
-/

@[expose] public section

namespace PartitionZheng

/-- The total weight of the residue classes the congruence admits for the outer
coefficient, with the `a * c ≡ 0` count taken twice, once for each of
`b ≡ 1, 5 [MOD 6]`. -/
@[pz_tag "def_weight"]
def weight (a : ℤ) : ℕ :=
  2 * (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 0).card
    + (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 2).card

/-- `weight` reads its argument only through `ZMod 6`, so it is periodic with
period `6`. -/
theorem weight_eq_of_cast {a a' : ℤ} (h : (a : ZMod 6) = (a' : ZMod 6)) :
    weight a = weight a' := by
  unfold weight; rw [h]

/-- The six values of the weight: `12, 3, 6, 6, 6, 3` for
`a ≡ 0, 1, 2, 3, 4, 5 [MOD 6]`. -/
@[pz_tag "lem_weight_values"]
theorem weight_values :
    weight 0 = 12 ∧ weight 1 = 3 ∧ weight 2 = 6 ∧
    weight 3 = 6 ∧ weight 4 = 6 ∧ weight 5 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The weight sums to `36` over a period, so its mean is `6`. -/
@[pz_tag "lem_weight_sum"]
theorem weight_sum :
    weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5 = 36 := by
  decide

end PartitionZheng
