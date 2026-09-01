/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import PartitionZheng.Meta.Attr

/-!
# Congruences modulo 24

The discriminant condition `4ac - b^2 ≡ 23 [ZMOD 24]` is turned into conditions
on `b` and on `a * c` modulo `6`. Everything here is elementary: squares of
integers coprime to `6` are `1` modulo `24`, and squares of odd multiples of `3`
are `9`.

The coprimality hypotheses are written `¬ (2 ∣ d)` and `¬ (3 ∣ d)` rather than
`Int.gcd d 6 = 1`. The two are equivalent, and the unfolded form is what every
consumer here has to hand.

## Main results

* `PartitionZheng.sq_emod_24` — `d` coprime to `6` gives `d ^ 2 % 24 = 1`.
* `PartitionZheng.sq_emod_24_of_three_dvd` — `b` odd with `3 ∣ b` gives
  `b ^ 2 % 24 = 9`.
* `PartitionZheng.odd_of_disc` — the discriminant congruence forces `b` odd.
* `PartitionZheng.coprime_six_of_sq_dvd` — a square divisor of an integer
  congruent to `23` modulo `24` is coprime to `6`.
-/

@[expose] public section

namespace PartitionZheng

/-- Reduce a claim about `d ^ 2 % 24` to the same claim about the residue
`d % 24`, which `interval_cases` can then check outright. -/
private lemma sq_emod_24_eq {d v : ℤ} (h : (d % 24) ^ 2 % 24 = v) :
    d ^ 2 % 24 = v := by
  have hmod : ((d % 24) ^ 2) ≡ d ^ 2 [ZMOD 24] := (Int.mod_modEq d 24).pow 2
  calc d ^ 2 % 24 = (d % 24) ^ 2 % 24 := hmod.symm
    _ = v := h

/-- The 24 residues, checked one at a time: an odd residue not divisible by `3`
squares to `1`. -/
private lemma residue_sq_one {r : ℤ} (h0 : 0 ≤ r) (h1 : r < 24)
    (h2 : r % 2 = 1) (h3 : r % 3 ≠ 0) : r ^ 2 % 24 = 1 := by
  interval_cases r <;> simp_all

/-- The 24 residues again: an odd residue divisible by `3` squares to `9`. -/
private lemma residue_sq_nine {r : ℤ} (h0 : 0 ≤ r) (h1 : r < 24)
    (h2 : r % 2 = 1) (h3 : r % 3 = 0) : r ^ 2 % 24 = 9 := by
  interval_cases r <;> simp_all

/-- `d % 24` has the same parity and the same residue modulo `3` as `d`, since
`2` and `3` both divide `24`. -/
private lemma emod_24_bounds (d : ℤ) :
    0 ≤ d % 24 ∧ d % 24 < 24 ∧ d % 24 % 2 = d % 2 ∧ d % 24 % 3 = d % 3 :=
  ⟨Int.emod_nonneg d (by norm_num), Int.emod_lt_of_pos d (by norm_num),
    Int.emod_emod_of_dvd d (by norm_num), Int.emod_emod_of_dvd d (by norm_num)⟩

/-- Squares of integers coprime to `6` are `1` modulo `24`. -/
@[pz_tag "lem_dsq_mod24"]
theorem sq_emod_24 {d : ℤ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) : d ^ 2 % 24 = 1 := by
  obtain ⟨hr0, hr1, e2, e3⟩ := emod_24_bounds d
  have h2' : d % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one d with h | h
    · exact absurd (Int.dvd_of_emod_eq_zero h) h2
    · exact h
  have h3' : d % 3 ≠ 0 := fun h => h3 (Int.dvd_of_emod_eq_zero h)
  exact sq_emod_24_eq (residue_sq_one hr0 hr1 (by rw [e2]; exact h2') (by rw [e3]; exact h3'))

/-- Squares of odd multiples of `3` are `9` modulo `24`. Together with
`sq_emod_24` this is the two-case computation the discriminant congruence needs. -/
@[pz_tag "lem_bsq_mod24"]
theorem sq_emod_24_of_three_dvd {b : ℤ} (hodd : Odd b) (h3 : 3 ∣ b) :
    b ^ 2 % 24 = 9 := by
  obtain ⟨hr0, hr1, e2, e3⟩ := emod_24_bounds b
  have h2' : b % 2 = 1 := Int.odd_iff.mp hodd
  have h3' : b % 3 = 0 := Int.emod_eq_zero_of_dvd h3
  exact sq_emod_24_eq (residue_sq_nine hr0 hr1 (by rw [e2]; exact h2') (by rw [e3]; exact h3'))

/-- The discriminant congruence forces the middle coefficient to be odd:
modulo `2` it reads `-b ^ 2 ≡ 1`. -/
@[pz_tag "lem_b_odd"]
theorem odd_of_disc {a b c : ℤ} (h : (4 * a * c - b ^ 2) % 24 = 23) : Odd b := by
  rcases Int.even_or_odd b with he | ho
  · obtain ⟨k, hk⟩ := he
    obtain ⟨t, ht⟩ : (2 : ℤ) ∣ (4 * a * c - b ^ 2) :=
      ⟨2 * a * c - 2 * k ^ 2, by subst hk; ring⟩
    rw [ht] at h
    omega
  · exact ho

/-- A square divisor of an integer congruent to `23` modulo `24` is coprime to
`6`: such an integer is odd and is `2` modulo `3`. -/
@[pz_tag "lem_d_coprime6"]
theorem coprime_six_of_sq_dvd {N d : ℤ} (hN : N % 24 = 23) (hdvd : d ^ 2 ∣ N) :
    ¬ (2 ∣ d) ∧ ¬ (3 ∣ d) := by
  have hd : d ∣ N := dvd_trans (dvd_pow_self d (by norm_num)) hdvd
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · obtain ⟨t, ht⟩ := dvd_trans h2 hd
    omega
  · obtain ⟨t, ht⟩ := dvd_trans h3 hd
    omega

/-- With `b` coprime to `3`, the discriminant congruence says exactly that
`6 ∣ a * c`. This is the first case of the two-case reduction. -/
@[pz_tag "lem_congruence_ac"]
theorem disc_emod_iff_of_not_three_dvd {a b c : ℤ} (hb : Odd b) (h3 : ¬ (3 ∣ b)) :
    (4 * (a * c) - b ^ 2) % 24 = 23 ↔ (a * c) % 6 = 0 := by
  have h2 : ¬ (2 ∣ b) := by
    intro h
    have hodd := Int.odd_iff.mp hb
    omega
  have hb2 : b ^ 2 % 24 = 1 := sq_emod_24 h2 h3
  omega

/-- With `3 ∣ b`, the discriminant congruence says exactly that
`a * c ≡ 2 [ZMOD 6]`. This is the second case of the two-case reduction. -/
@[pz_tag "lem_congruence_ac"]
theorem disc_emod_iff_of_three_dvd {a b c : ℤ} (hb : Odd b) (h3 : 3 ∣ b) :
    (4 * (a * c) - b ^ 2) % 24 = 23 ↔ (a * c) % 6 = 2 := by
  have hb2 : b ^ 2 % 24 = 9 := sq_emod_24_of_three_dvd hb h3
  omega

/-- **Stripping the square factor from the congruence.** For `d` coprime to `6`,
`d² r ≡ 23 [ZMOD 24]` exactly when `r ≡ 23 [ZMOD 24]`, since `d² ≡ 1 [ZMOD 24]`.

This is what lets the count of admissible discriminants replace the condition
`d² r ≡ 23 (24)` on `N = d² r` by a condition on `r` alone, so that the inner
count becomes a residue count in a fixed class and
`card_residue_class_Icc_mod` applies at `q = 24`. -/
theorem dsq_mul_emod_24 {d r : ℤ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    (d ^ 2 * r) % 24 = 23 ↔ r % 24 = 23 := by
  have hd : d ^ 2 % 24 = 1 := sq_emod_24 h2 h3
  rw [Int.mul_emod, hd, one_mul, Int.emod_emod_of_dvd r (dvd_refl 24)]

/-! ### Natural-number forms

The count of admissible discriminants works over `ℕ` — `admissible` is a
`Finset ℕ` and the fibre map is `r ↦ d² * r` on naturals — so the two
congruence facts are needed there too. They are cast from the `ℤ` versions
rather than reproved. -/

/-- `sq_emod_24` over `ℕ`. -/
theorem sq_emod_24_nat {d : ℕ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    d ^ 2 % 24 = 1 := by
  have h2' : ¬ ((2 : ℤ) ∣ (d : ℤ)) := fun h => h2 (by exact_mod_cast h)
  have h3' : ¬ ((3 : ℤ) ∣ (d : ℤ)) := fun h => h3 (by exact_mod_cast h)
  have hz : ((d : ℤ)) ^ 2 % 24 = 1 := sq_emod_24 h2' h3'
  have hcast : ((d ^ 2 % 24 : ℕ) : ℤ) = 1 := by push_cast; exact hz
  exact_mod_cast hcast

/-- `dsq_mul_emod_24` over `ℕ`: for `d` coprime to `6`, `d² r ≡ 23 [MOD 24]`
exactly when `r ≡ 23 [MOD 24]`. This is what lets the fibre over `d` be counted
as a residue class in `r` alone. -/
theorem dsq_mul_emod_24_nat {d r : ℕ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    (d ^ 2 * r) % 24 = 23 ↔ r % 24 = 23 := by
  have hd : d ^ 2 % 24 = 1 := sq_emod_24_nat h2 h3
  rw [Nat.mul_mod, hd, one_mul, Nat.mod_mod]

end PartitionZheng
