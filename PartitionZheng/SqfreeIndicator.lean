/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Real.Basic
public import PartitionZheng.Meta.Attr

/-!
# The square-free indicator as a Möbius sum

`∑_{d² ∣ N} μ(d) = 1` when `N` is square-free and `0` otherwise. Mathlib has
`μ n ^ 2 = if Squarefree n then 1 else 0` but not this sum form, which is what
the count of admissible discriminants inserts and then swaps.

The proof goes through `P = ∏ {p prime : p² ∣ N} p`. Only square-free `d`
contribute to the sum, and for square-free `d` the conditions `d² ∣ N` and
`d ∣ P` agree — both say `d.factorization p ≤ 1` exactly where `p² ∣ N`. So the
sum collapses to `∑_{d ∣ P} μ d`, which is `1` iff `P = 1`, which is iff `N` is
square-free.

## Main results

* `PartitionZheng.sum_moebius_divisors` — `∑_{d ∣ n} μ d = if n = 1 then 1 else 0`.
* `PartitionZheng.sqfree_indicator` — the identity.
-/

@[expose] public section

namespace PartitionZheng

open ArithmeticFunction Finset
-- the `μ` notation is scoped to the NESTED namespace, not to `ArithmeticFunction`
open scoped ArithmeticFunction.Moebius

/-- `∑_{d ∣ n} μ d = 1` if `n = 1` and `0` otherwise: the Dirichlet convolution
`μ * ζ = 1` read off pointwise. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  -- Rewrite the goal's own left side into `(μ * ζ) n` and collapse it; this
  -- never names ζ (its notation is scoped elsewhere again) and never risks simp
  -- flattening the hypothesis to `True`.
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

/-- The product of the primes whose square divides `N`. -/
def sqPrimes (N : ℕ) : ℕ := ∏ p ∈ N.primeFactors with p ^ 2 ∣ N, p

/-- `sqPrimes N = 1` exactly when `N` is square-free. -/
theorem sqPrimes_eq_one_iff {N : ℕ} (hN : N ≠ 0) :
    sqPrimes N = 1 ↔ Squarefree N := by
  classical
  rw [Nat.squarefree_iff_factorization_le_one hN]
  constructor
  · intro h p
    by_contra hc
    have h2 : 2 ≤ N.factorization p := by omega
    have hp : p.Prime := by
      by_contra hnp
      rw [Nat.factorization_eq_zero_of_not_prime N hnp] at h2
      omega
    have hpd : p ∣ N := Nat.dvd_of_factorization_pos (by omega)
    have hmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hN⟩
    have hsq : p ^ 2 ∣ N := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mpr h2
    have : p ∈ N.primeFactors.filter (fun q => q ^ 2 ∣ N) :=
      Finset.mem_filter.mpr ⟨hmem, hsq⟩
    have hdvd : p ∣ sqPrimes N := Finset.dvd_prod_of_mem _ this
    rw [h] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  · intro h
    have : N.primeFactors.filter (fun q => q ^ 2 ∣ N) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro p hmem hsq
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      have := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mp hsq
      have := h p
      omega
    rw [sqPrimes, this, Finset.prod_empty]

/-- The factorization of `sqPrimes N`: exponent `1` at each prime whose square
divides `N`, and `0` elsewhere. -/
theorem sqPrimes_factorization (N q : ℕ) :
    (sqPrimes N).factorization q =
      if q ∈ N.primeFactors.filter (fun p => p ^ 2 ∣ N) then 1 else 0 := by
  classical
  have hne : ∀ p ∈ N.primeFactors.filter (fun p => p ^ 2 ∣ N), p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero
  rw [sqPrimes, Nat.factorization_prod hne]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).factorization,
      Finsupp.single_apply])]
  by_cases hq : q ∈ N.primeFactors.filter (fun p => p ^ 2 ∣ N)
  · rw [ite_eq_left hq, Finset.sum_eq_single q]
    · simp
    · intro b _ hbq; exact ite_eq_right hbq
    · intro h; exact absurd hq h
  · rw [ite_eq_right hq, Finset.sum_eq_zero]
    intro b hb
    have : b ≠ q := fun hc => hq (hc ▸ hb)
    simp [this]

/-- For square-free `d`, the conditions `d ^ 2 ∣ N` and `d ∣ sqPrimes N` agree:
both say `d.factorization p ≤ 1` exactly where `p ^ 2 ∣ N`. -/
theorem sq_dvd_iff_dvd_sqPrimes {N d : ℕ} (hN : N ≠ 0) (hd : d ≠ 0)
    (hdsq : Squarefree d) : d ^ 2 ∣ N ↔ d ∣ sqPrimes N := by
  classical
  have hsp : sqPrimes N ≠ 0 := by
    rw [sqPrimes]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) hN,
    ← Nat.factorization_le_iff_dvd hd hsp]
  constructor
  · intro h p
    rw [sqPrimes_factorization]
    have h2 : 2 * d.factorization p ≤ N.factorization p := by
      have := h p
      rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at this
    have hle1 : d.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hd).mp hdsq p
    by_cases hmem : p ∈ N.primeFactors.filter (fun r => r ^ 2 ∣ N)
    · rw [ite_eq_left hmem]; exact hle1
    · rw [ite_eq_right hmem]
      by_contra hc
      have hdp : 1 ≤ d.factorization p := by omega
      have hp : p.Prime := Nat.prime_of_mem_primeFactors
        (Nat.mem_primeFactors.mpr ⟨by
          by_contra hnp
          rw [Nat.factorization_eq_zero_of_not_prime d hnp] at hdp; omega,
          Nat.dvd_of_factorization_pos (by omega), hd⟩)
      have hpN : p ^ 2 ∣ N := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mpr (by omega)
      exact hmem (Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_trans (dvd_pow_self p two_ne_zero) hpN, hN⟩, hpN⟩)
  · intro h p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hsp' := h p
    rw [sqPrimes_factorization] at hsp'
    by_cases hmem : p ∈ N.primeFactors.filter (fun r => r ^ 2 ∣ N)
    · rw [ite_eq_left hmem] at hsp'
      have hpN : p ^ 2 ∣ N := (Finset.mem_filter.mp hmem).2
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hmem).1
      have : 2 ≤ N.factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mp hpN
      omega
    · rw [ite_eq_right hmem] at hsp'
      omega

/-- `sqPrimes N` is square-free: its factorization is `0` or `1` everywhere. -/
theorem sqPrimes_squarefree (N : ℕ) : Squarefree (sqPrimes N) := by
  classical
  have hsp : sqPrimes N ≠ 0 := by
    rw [sqPrimes]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  rw [Nat.squarefree_iff_factorization_le_one hsp]
  intro p
  rw [sqPrimes_factorization]
  split <;> norm_num

/-- **The square-free indicator as a Möbius sum.** For `N ≠ 0`,
`∑_{d ∣ N, d² ∣ N} μ d = 1` when `N` is square-free and `0` otherwise. -/
@[pz_tag "lem_sqfree_indicator"]
theorem sqfree_indicator {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors with d ^ 2 ∣ N, μ d = if Squarefree N then 1 else 0 := by
  classical
  have hsp : sqPrimes N ≠ 0 := by
    rw [sqPrimes]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  -- Only square-free `d` contribute, and those are exactly the divisors of
  -- `sqPrimes N`.
  have hset : (N.divisors.filter fun d => d ^ 2 ∣ N).filter (fun d => Squarefree d)
      = (sqPrimes N).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hdN, -⟩, hdsq⟩, hsf⟩
      exact ⟨(sq_dvd_iff_dvd_sqPrimes hN (by rintro rfl; simp at hdN; omega) hsf).mp hdsq, hsp⟩
    · rintro ⟨hdvd, -⟩
      have hd0 : d ≠ 0 := by rintro rfl; exact hsp (Nat.eq_zero_of_zero_dvd hdvd)
      have hsf : Squarefree d := (sqPrimes_squarefree N).squarefree_of_dvd hdvd
      have hdsq : d ^ 2 ∣ N := (sq_dvd_iff_dvd_sqPrimes hN hd0 hsf).mpr hdvd
      exact ⟨⟨⟨dvd_trans (dvd_pow_self d two_ne_zero) hdsq, hN⟩, hdsq⟩, hsf⟩
  -- Discard the non-square-free terms, on which `μ` vanishes.
  have hdrop : ∑ d ∈ (N.divisors.filter fun d => d ^ 2 ∣ N).filter (fun d => Squarefree d), μ d
      = ∑ d ∈ N.divisors.filter fun d => d ^ 2 ∣ N, μ d := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    by_contra hne
    exact hx (Finset.mem_filter.mpr ⟨‹_›, moebius_ne_zero_iff_squarefree.mp hne⟩)
  rw [← hdrop, hset, sum_moebius_divisors]
  -- Rewriting `sqPrimes N = 1` into `Squarefree N` under an `ite` breaks the
  -- motive (the `Decidable` instances differ), so case-split instead.
  by_cases h : Squarefree N
  · rw [ite_eq_left ((sqPrimes_eq_one_iff hN).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((sqPrimes_eq_one_iff hN).mp hc)), ite_eq_right h]

/-- **The Möbius double-sum exchange.** For any finite set `S` of integers and
any bound `M`,

`∑_{N ∈ S} ∑_{d ≤ M, d² ∣ N} μ(d) = ∑_{d ≤ M} μ(d) · #{N ∈ S : d² ∣ N}`.

This is the swap the count of admissible discriminants performs after inserting
`sqfree_indicator`: the left side counts square-free `N` one at a time, the
right side groups by the square divisor. It is pure double counting — the
condition `d² ∣ N` is symmetric in the two summation variables, so
`Finset.sum_comm` applies once both filters are turned into `ite`s.

Stating it over an explicit `Finset.range (M+1)` rather than `N.divisors` is
what makes the exchange possible at all: the divisor set depends on `N`, so the
inner index set would otherwise vary with the outer variable. -/
theorem sum_moebius_swap (S : Finset ℕ) (M : ℕ) :
    ∑ N ∈ S, ∑ d ∈ (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N),
        (μ d : ℝ)
      = ∑ d ∈ Finset.range (M + 1), (μ d : ℝ)
          * (((S.filter fun N => d ^ 2 ∣ N)).card : ℝ) := by
  classical
  -- turn both filters into `ite`s so the index sets no longer depend on each other
  have hL : ∀ N : ℕ, ∑ d ∈ (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N), (μ d : ℝ)
      = ∑ d ∈ Finset.range (M + 1), if d ^ 2 ∣ N then (μ d : ℝ) else 0 := by
    intro N; rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun N _ => hL N, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  -- the inner sum is `μ d` on the fibre and `0` off it
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end PartitionZheng
