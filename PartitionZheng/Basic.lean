/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import PartitionZheng.Meta.Attr

/-!
# The partition function and its odd-value counting function

This file fixes the two objects the corollary of Qi-Yang Zheng is stated about:
the partition function `p` and the counting function `N_odd`.

## Main definitions

* `PartitionZheng.pFun n` — the number of partitions of `n`.
* `PartitionZheng.Nodd X` — the number of `n ≤ X` with `p n` odd.
-/

@[expose] public section

namespace PartitionZheng

/-- The partition function `p n`: the number of partitions of `n`. -/
@[pz_tag "def_p"]
def pFun (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `Nodd X` counts the integers `0 ≤ n ≤ X` whose partition number is odd,
written `N_odd(X)` in the source. Oddness is spelled `pFun n % 2 = 1` so that
the predicate is decidable without an instance argument. -/
@[pz_tag "def_Nodd"]
def Nodd (X : ℕ) : ℕ :=
  ((Finset.range (X + 1)).filter fun n => pFun n % 2 = 1).card

end PartitionZheng
