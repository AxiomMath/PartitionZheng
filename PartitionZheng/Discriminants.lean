/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import PartitionZheng.Meta.Attr

/-!
# Admissible discriminants, and recovering one from a partition index

For square-free `D ≡ 23 [MOD 24]` the parity theorem produces an `n` with
`24 * n = D * m ^ 2 + 1` and `p n` odd. This file fixes the set of such `D` up
to a bound, and the square-free part, which is what recovers `D` from `n`.

## Main definitions

* `PartitionZheng.admissible` — the `D` with `1 < D ≤ Y`, `D ≡ 23 [MOD 24]`,
  `D` square-free.
* `PartitionZheng.sqfPart` — the product of the primes dividing `N` to an odd
  power.
-/

@[expose] public section

namespace PartitionZheng

/-- The admissible discriminants up to `Y`: square-free `D` with `1 < D ≤ Y` and
`D ≡ 23 [MOD 24]`. A `Finset` rather than a `Set`, since `D ≤ Y` bounds it and
the counting argument needs its cardinality. -/
@[pz_tag "def_Dset"]
noncomputable def admissible (Y : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Y⌋₊).filter fun D => D % 24 = 23 ∧ Squarefree D

/-- The square-free part of `N`: the product of the primes dividing `N` to an
odd power. Zheng's injectivity step recovers the discriminant as
`sqfPart (24 * n - 1)`. -/
@[pz_tag "def_sqf"]
noncomputable def sqfPart (N : ℕ) : ℕ :=
  N.primeFactors.prod fun q => if Odd (N.factorization q) then q else 1

/-- `D` is an admissible discriminant up to `Y` exactly when `2 ≤ D ≤ ⌊Y⌋₊`,
`D % 24 = 23` and `D` is square-free. -/
lemma mem_admissible {Y : ℝ} {D : ℕ} :
    D ∈ admissible Y ↔ (2 ≤ D ∧ D ≤ ⌊Y⌋₊) ∧ D % 24 = 23 ∧ Squarefree D := by
  simp [admissible, Finset.mem_filter, Finset.mem_Icc, and_assoc]

end PartitionZheng
