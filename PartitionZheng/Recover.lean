/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.Squarefree
public import PartitionZheng.Discriminants

/-!
# Recovering the discriminant from the partition index

Zheng's injectivity step: the map `D ↦ n_D` is injective because `D` can be
recovered from `n_D`. Concretely `24 * n - 1 = D * m ^ 2`, and since `D` is
square-free the primes dividing `D * m ^ 2` to an odd power are exactly those
dividing `D`, whose product is `D` again.

## Main results

* `PartitionZheng.odd_factorization_iff` — the exponent of `q` in `D * m ^ 2`
  is odd exactly when `q ∣ D`.
* `PartitionZheng.sqfPart_mul_sq` — hence `sqfPart (D * m ^ 2) = D`.
* `PartitionZheng.recover_disc` — hence `sqfPart (24 * n - 1) = D`.
-/

@[expose] public section

namespace PartitionZheng

/-- For square-free `D` and `m ≠ 0`, the exponent of a prime `q` in `D * m ^ 2`
is odd exactly when `q ∣ D`: the exponent is `D.factorization q + 2 * _`, and
square-freeness pins the first summand to `0` or `1`. -/
theorem odd_factorization_iff {D m q : ℕ} (hD : Squarefree D) (hm : m ≠ 0)
    (hq : q.Prime) :
    Odd ((D * m ^ 2).factorization q) ↔ q ∣ D := by
  have hD0 : D ≠ 0 := hD.ne_zero
  have hpow : (m ^ 2) ≠ 0 := pow_ne_zero 2 hm
  have hfac : (D * m ^ 2).factorization q
      = D.factorization q + 2 * m.factorization q := by
    rw [Nat.factorization_mul hD0 hpow, Nat.factorization_pow]
    simp
  have hle : D.factorization q ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hD0).mp hD q
  rw [hfac, Nat.odd_iff, hq.dvd_iff_one_le_factorization hD0]
  omega

/-- The square-free part of `D * m ^ 2` is `D`, for square-free `D`. -/
theorem sqfPart_mul_sq {D m : ℕ} (hD : Squarefree D) (hm : m ≠ 0) :
    sqfPart (D * m ^ 2) = D := by
  have hD0 : D ≠ 0 := hD.ne_zero
  have hpow : (m ^ 2) ≠ 0 := pow_ne_zero 2 hm
  have hne : D * m ^ 2 ≠ 0 := mul_ne_zero hD0 hpow
  unfold sqfPart
  -- Replace the parity test by divisibility of `D`, which is what it means.
  have hstep : ∀ q ∈ (D * m ^ 2).primeFactors,
      (if Odd ((D * m ^ 2).factorization q) then q else 1)
        = (if q ∣ D then q else 1) := by
    intro q hq
    have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
    by_cases hdvd : q ∣ D
    · have : Odd ((D * m ^ 2).factorization q) :=
        (odd_factorization_iff hD hm hqp).mpr hdvd
      simp [this, hdvd]
    · have hnodd : ¬ Odd ((D * m ^ 2).factorization q) := fun h =>
        hdvd ((odd_factorization_iff hD hm hqp).mp h)
      simp [hnodd, hdvd]
  rw [Finset.prod_congr rfl hstep, ← Finset.prod_filter]
  -- The primes of `D * m ^ 2` that divide `D` are exactly the primes of `D`.
  have hfilter : ((D * m ^ 2).primeFactors.filter fun q => q ∣ D) = D.primeFactors := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hqp, _, _⟩, hdvd⟩
      exact ⟨hqp, hdvd, hD0⟩
    · rintro ⟨hqp, hdvd, _⟩
      exact ⟨⟨hqp, hdvd.trans (dvd_mul_right D (m ^ 2)), hne⟩, hdvd⟩
  rw [hfilter, Nat.prod_primeFactors_of_squarefree hD]

/-- The discriminant is recovered from the partition index: if `D` is square-free
and `24 * n = D * m ^ 2 + 1`, then `sqfPart (24 * n - 1) = D`. This is what
makes `D ↦ n_D` injective. -/
@[pz_tag "lem_recover_D"]
theorem recover_disc {D m n : ℕ} (hD : Squarefree D) (hm : m ≠ 0)
    (h : 24 * n = D * m ^ 2 + 1) : sqfPart (24 * n - 1) = D := by
  have : 24 * n - 1 = D * m ^ 2 := by omega
  rw [this]
  exact sqfPart_mul_sq hD hm

end PartitionZheng
