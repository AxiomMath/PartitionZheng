/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.Congruence
public import PartitionZheng.Constants
public import PartitionZheng.Discriminants
public import PartitionZheng.EulerProduct
public import PartitionZheng.SqfreeIndicator

/-!
# Counting the admissible discriminants

`|#D(Y) - δY| ≤ C√Y` with `δ = 3/(8π²)` and the explicit constant `C = 7`. The
argument inserts `sqfree_indicator` to turn the square-free condition into a
divisor sum, swaps the order of summation, counts each inner residue class, and
evaluates the resulting series.

## Main definitions

* `PartitionZheng.mainTerm` — the per-`d` main term `(⌊Y⌋₊ / d²) / 24`.
* `PartitionZheng.mainTermReal` — the same with both roundings removed.
* `PartitionZheng.coprimeTerm` — `μ(d)/d²` on the `d` coprime to `6`, else `0`.

## Main results

* `PartitionZheng.card_admissible_eq_sum` — the count as a Möbius double sum.
* `PartitionZheng.card_admissible_eq_swapped` — the count with the sums swapped.
* `PartitionZheng.card_admissible_sub_mainSum_le` — the count against its main
  sum.
* `PartitionZheng.card_admissible_sub_delta_le` — `|#D(Y) - δY| ≤ 7√Y`.
-/

@[expose] public section

namespace PartitionZheng

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- The admissible discriminants are the square-free elements of the residue
class, so `#D(Y)` is the double sum obtained from `sqfree_indicator`. -/
theorem card_admissible_eq_sum (Y : ℝ) :
    ((admissible Y).card : ℝ)
      = ∑ N ∈ (Finset.Icc 2 ⌊Y⌋₊).filter (fun N : ℕ => N % 24 = 23),
          ∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), (μ d : ℝ) := by
  classical
  -- split the two conditions of `admissible`
  have hset : admissible Y
      = ((Finset.Icc 2 ⌊Y⌋₊).filter fun N : ℕ => N % 24 = 23).filter
          (fun N => Squarefree N) := by
    unfold admissible
    rw [Finset.filter_filter]
  rw [hset, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun N hN => ?_
  -- `N ≥ 2`, so `sqfree_indicator` applies
  have hN0 : N ≠ 0 := by
    have h1 := (Finset.mem_filter.mp hN).1
    have h2 := Finset.mem_Icc.mp h1
    omega
  have hZ := sqfree_indicator hN0
  have hcast : ∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), (μ d : ℝ)
      = (((∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), μ d : ℤ)) : ℝ) := by
    push_cast; ring
  rw [hcast, hZ]
  split <;> norm_num

/-- The inner index set may be taken to be a fixed range. For `N ≤ M²` the
divisors `d` with `d² ∣ N` are exactly the `d ≤ M` with `d² ∣ N`, since
`d² ∣ N` forces `d² ≤ N ≤ M²`.

Over `N.divisors` the inner index set depends on `N`, so the order of summation
cannot be exchanged; over a fixed range it can. -/
theorem divisor_filter_eq_range {N M : ℕ} (hN : N ≠ 0) (hM : N ≤ M ^ 2) :
    N.divisors.filter (fun d => d ^ 2 ∣ N)
      = (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N) := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨-, -⟩, hsq⟩
    refine ⟨?_, hsq⟩
    -- `d² ∣ N` gives `d² ≤ N ≤ M²`, hence `d ≤ M`
    have hle : d ^ 2 ≤ N := Nat.le_of_dvd (by omega) hsq
    by_contra hc
    have hMd : M < d := by omega
    have : M ^ 2 < d ^ 2 := Nat.pow_lt_pow_left hMd (by norm_num)
    omega
  · rintro ⟨-, hsq⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp only [pow_two, Nat.mul_zero] at hsq
      exact hN (Nat.eq_zero_of_zero_dvd hsq)
    exact ⟨⟨dvd_trans (dvd_pow_self d two_ne_zero) hsq, hN⟩, hsq⟩

/-- **The fibre over `d`.** For `d ≥ 1` coprime to `6`, the `N ≤ M` in the class
`23` modulo `24` divisible by `d²` correspond bijectively, via `N = d² r`, to the
`r ≤ M / d²` in the class `23` modulo `24`.

The lower bound `2 ≤ N` of `admissible` is automatic here and costs nothing:
`N ≡ 23 [MOD 24]` already forces `N ≥ 23`. -/
theorem fibre_card {M d : ℕ} (hd : 1 ≤ d) (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    (((Finset.Icc 2 M).filter fun N => N % 24 = 23).filter (fun N => d ^ 2 ∣ N)).card
      = ((Finset.Icc 1 (M / d ^ 2)).filter fun r => r % 24 = 23).card := by
  classical
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  refine Finset.card_bij' (fun N _ => N / d ^ 2) (fun r _ => d ^ 2 * r) ?_ ?_ ?_ ?_
  · -- `N ↦ N / d²` lands in the `r`-set
    intro N hN
    obtain ⟨hN1, hdvd⟩ := Finset.mem_filter.mp hN
    obtain ⟨hNIcc, hN23⟩ := Finset.mem_filter.mp hN1
    obtain ⟨-, hNM⟩ := Finset.mem_Icc.mp hNIcc
    obtain ⟨k, hk⟩ := hdvd
    have hkey : N / d ^ 2 = k := by rw [hk]; exact Nat.mul_div_cancel_left k hd2
    have hk23 : k % 24 = 23 := by
      rw [hk] at hN23; exact (dsq_mul_emod_24_nat h2 h3).mp hN23
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · change 1 ≤ N / d ^ 2
      rw [hkey]; omega
    · rw [hkey, Nat.le_div_iff_mul_le hd2, Nat.mul_comm]
      rw [hk] at hNM
      exact hNM
    · rw [hkey]; exact hk23
  · -- `r ↦ d² r` lands in the `N`-set
    intro r hr
    obtain ⟨hrIcc, hr23⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hrM⟩ := Finset.mem_Icc.mp hrIcc
    have h23 : (d ^ 2 * r) % 24 = 23 := (dsq_mul_emod_24_nat h2 h3).mpr hr23
    have hle : d ^ 2 * r ≤ M := by
      have hstep : d ^ 2 * r ≤ d ^ 2 * (M / d ^ 2) := Nat.mul_le_mul_left _ hrM
      have hdiv : d ^ 2 * (M / d ^ 2) ≤ M := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self M (d ^ 2)
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by change 2 ≤ d ^ 2 * r; omega, hle⟩, h23⟩, Dvd.intro r rfl⟩
  · -- `d² * (N / d²) = N`
    intro N hN
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.mp hN
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left k hd2]
  · -- `(d² * r) / d² = r`
    intro r _
    exact Nat.mul_div_cancel_left r hd2

/-- **The residue count over `ℕ`, modulus `24`.** For `lo ≤ hi`, the naturals of
`Finset.Icc lo hi` congruent to `r` modulo `24` number at most
`(hi - lo) / 24 + 1`. -/
theorem card_residue_class_Icc_nat24 {lo hi r : ℕ} (hle : lo ≤ hi) :
    ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ)
      ≤ ((hi : ℝ) - (lo : ℝ)) / 24 + 1 := by
  classical
  -- inject `c ↦ (c - lo) / 24` into `range ((hi - lo) / 24 + 1)`
  have hkey : ((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r).card
      ≤ (Finset.range ((hi - lo) / 24 + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun c => (c - lo) / 24) (fun c hc => ?_) ?_
    · obtain ⟨hIcc, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
      refine Finset.mem_range.mpr ?_
      change (c - lo) / 24 < (hi - lo) / 24 + 1
      omega
    · intro c hc c' hc' h
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hc hc'
      obtain ⟨⟨hc1, hc2⟩, hcr⟩ := hc
      obtain ⟨⟨hc1', hc2'⟩, hcr'⟩ := hc'
      simp only at h
      omega
  -- `#range n = n`, and `ℕ`-division is bounded by real division
  have hcard : ((Finset.range ((hi - lo) / 24 + 1)).card : ℝ)
      = (((hi - lo) / 24 : ℕ) : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hdiv : (((hi - lo) / 24 : ℕ) : ℝ) ≤ ((hi : ℝ) - (lo : ℝ)) / 24 := by
    have hz : (24 : ℕ) * ((hi - lo) / 24) ≤ hi - lo := Nat.mul_div_le (hi - lo) 24
    have hzR : (24 : ℝ) * (((hi - lo) / 24 : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := by
      exact_mod_cast hz
    have hsub : ((hi - lo : ℕ) : ℝ) = (hi : ℝ) - (lo : ℝ) := by
      have : (lo : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hle
      push_cast [Nat.cast_sub hle]; ring
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 24)]
    rw [hsub] at hzR
    linarith
  have hmono : ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ)
      ≤ ((Finset.range ((hi - lo) / 24 + 1)).card : ℝ) := by exact_mod_cast hkey
  rw [hcard] at hmono
  linarith

/-- **The residue count over `ℕ`, lower bound.** For `r < 24`, the naturals of
`Finset.Icc lo hi` congruent to `r` modulo `24` number at least
`(hi - lo) / 24 - 1`.

The witness is the arithmetic progression starting at the least `lo' ≥ lo` in the
class, namely `lo' = lo + (r + 24 - lo % 24) % 24`, so `lo ≤ lo' ≤ lo + 23`. -/
theorem card_residue_class_Icc_nat24_ge {lo hi r : ℕ} (hr : r < 24) :
    ((hi : ℝ) - (lo : ℝ)) / 24 - 1
      ≤ ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ) := by
  classical
  set s : ℕ := (r + 24 - lo % 24) % 24 with hs
  set lo' : ℕ := lo + s with hlo'
  have hslt : s < 24 := by rw [hs]; omega
  have hsr : lo' % 24 = r := by rw [hlo', hs]; omega
  rcases le_or_gt lo' hi with hle' | hgt
  · set n : ℕ := (hi - lo') / 24 + 1 with hn
    have hinjf : Function.Injective (fun j : ℕ => lo' + 24 * j) := by
      intro a b h
      simp only at h
      omega
    have hsub : (Finset.range n).image (fun j : ℕ => lo' + 24 * j)
        ⊆ (Finset.Icc lo hi).filter (fun c : ℕ => c % 24 = r) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hjlt : j < n := Finset.mem_range.mp hj
      rw [hn] at hjlt
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    have himg : ((Finset.range n).image (fun j : ℕ => lo' + 24 * j)).card = n := by
      rw [Finset.card_image_of_injective _ hinjf, Finset.card_range]
    have hle : n ≤ ((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r).card := by
      have hcc := Finset.card_le_card hsub
      rwa [himg] at hcc
    have hkey : hi ≤ lo + 24 * n + 23 := by rw [hn]; omega
    have hkeyR : (hi : ℝ) ≤ (lo : ℝ) + 24 * (n : ℝ) + 23 := by exact_mod_cast hkey
    have hleR : (n : ℝ)
        ≤ ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ) := by
      exact_mod_cast hle
    linarith
  · -- `lo' > hi` forces `hi - lo < 24`, so the bound is negative
    have hlt : hi < lo + 24 := by omega
    have hnn : (0 : ℝ)
        ≤ ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ) :=
      Nat.cast_nonneg _
    have hR : (hi : ℝ) < (lo : ℝ) + 24 := by exact_mod_cast hlt
    linarith

/-- **The non-coprime fibres are empty.** If `2 ∣ d` or `3 ∣ d` then no `N` in
the class `23` modulo `24` is divisible by `d²`.

This is `coprime_six_of_sq_dvd` read contrapositively. The `d = 0` case is
covered, since `2 ∣ 0`. -/
theorem fibre_empty_of_not_coprime {M d : ℕ} (h : 2 ∣ d ∨ 3 ∣ d) :
    ((Finset.Icc 2 M).filter fun N => N % 24 = 23).filter (fun N => d ^ 2 ∣ N)
      = ∅ := by
  classical
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro N hN hdvd
  obtain ⟨hNIcc, hN23⟩ := Finset.mem_filter.mp hN
  -- transfer the two hypotheses to `ℤ` and apply `coprime_six_of_sq_dvd`
  have hNz : ((N : ℤ)) % 24 = 23 := by
    have : ((N % 24 : ℕ) : ℤ) = ((23 : ℕ) : ℤ) := by exact_mod_cast hN23
    push_cast at this
    omega
  have hdz : ((d : ℤ)) ^ 2 ∣ (N : ℤ) := by
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨(k : ℤ), by exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hk⟩
  obtain ⟨h2, h3⟩ := coprime_six_of_sq_dvd hNz hdz
  rcases h with hd | hd
  · exact h2 (by exact_mod_cast hd)
  · exact h3 (by exact_mod_cast hd)

/-- **The swapped form of the count.** For any `M` with `⌊Y⌋₊ ≤ M²`,

`#D(Y) = ∑_{d ≤ M} μ(d) · #{N ≤ ⌊Y⌋₊ : N ≡ 23 (24), d² ∣ N}`.

The hypothesis `⌊Y⌋₊ ≤ M²` is what makes the fixed inner range legal, and it
fails for `M = ⌊√Y⌋₊`: at `Y = 10` that gives `M² = 9 < 10`. It holds for
`M = ⌊√Y⌋₊ + 1`. -/
theorem card_admissible_eq_swapped (Y : ℝ) {M : ℕ} (hM : ⌊Y⌋₊ ≤ M ^ 2) :
    ((admissible Y).card : ℝ)
      = ∑ d ∈ Finset.range (M + 1), (μ d : ℝ)
          * ((((Finset.Icc 2 ⌊Y⌋₊).filter fun N : ℕ => N % 24 = 23).filter
              fun N => d ^ 2 ∣ N).card : ℝ) := by
  classical
  rw [card_admissible_eq_sum Y]
  have hinner : ∀ N ∈ (Finset.Icc 2 ⌊Y⌋₊).filter (fun N : ℕ => N % 24 = 23),
      ∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), (μ d : ℝ)
        = ∑ d ∈ (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N), (μ d : ℝ) := by
    intro N hN
    obtain ⟨hIcc, -⟩ := Finset.mem_filter.mp hN
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
    rw [divisor_filter_eq_range (M := M) (by omega) (by omega)]
  rw [Finset.sum_congr rfl hinner]
  exact sum_moebius_swap _ M

/-- **The per-`d` estimate.** For `d ≥ 1` coprime to `6`, the fibre over `d`
differs from `(M / d²) / 24` by at most `2`.

The constant `2` rather than `1` absorbs the `(K - 1)` versus `K` discrepancy in
the interval `Icc 1 K`, which costs `1/24`. -/
theorem fibre_approx {M d : ℕ} (hd : 1 ≤ d) (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    |((((Finset.Icc 2 M).filter fun N => N % 24 = 23).filter
        fun N => d ^ 2 ∣ N).card : ℝ) - ((M / d ^ 2 : ℕ) : ℝ) / 24| ≤ 2 := by
  classical
  rw [fibre_card hd h2 h3]
  set K : ℕ := M / d ^ 2 with hK
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  -- lower bound holds unconditionally
  have hge : ((K : ℝ) - 1) / 24 - 1
      ≤ ((((Finset.Icc 1 K).filter fun r : ℕ => r % 24 = 23)).card : ℝ) := by
    have h := card_residue_class_Icc_nat24_ge (lo := 1) (hi := K) (r := 23)
      (by norm_num)
    push_cast at h ⊢
    linarith
  -- upper bound needs `1 ≤ K`; for `K = 0` the set is empty
  have hle : ((((Finset.Icc 1 K).filter fun r : ℕ => r % 24 = 23)).card : ℝ)
      ≤ ((K : ℝ) - 1) / 24 + 1 := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK1
    · rw [hK0]
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)]
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, Nat.cast_zero]
      norm_num
    · have h := card_residue_class_Icc_nat24 (lo := 1) (hi := K) (r := 23) (by omega)
      push_cast at h ⊢
      linarith
  rw [abs_le]
  constructor <;> [linarith; linarith]

/-- **The aggregation.** If `f` and `g` agree to within `E` at every index and
the weights are bounded by `1`, then the weighted sums agree to within
`E * (M + 1)`.

No `0 ≤ E` hypothesis is needed: `hfg` at `d = 0` gives it, since
`Finset.range (M + 1)` is never empty. -/
theorem sum_weighted_error_le {M : ℕ} {E : ℝ} (f g w : ℕ → ℝ)
    (hfg : ∀ d ∈ Finset.range (M + 1), |f d - g d| ≤ E)
    (hw : ∀ d, |w d| ≤ 1) :
    |∑ d ∈ Finset.range (M + 1), w d * f d
      - ∑ d ∈ Finset.range (M + 1), w d * g d| ≤ E * ((M : ℝ) + 1) := by
  have hcomb : ∑ d ∈ Finset.range (M + 1), w d * f d
      - ∑ d ∈ Finset.range (M + 1), w d * g d
      = ∑ d ∈ Finset.range (M + 1), w d * (f d - g d) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hcomb]
  calc |∑ d ∈ Finset.range (M + 1), w d * (f d - g d)|
      ≤ ∑ d ∈ Finset.range (M + 1), |w d * (f d - g d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.range (M + 1), E := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [abs_mul]
        have h1 := hw d
        have h2 := hfg d hd
        have hnn : 0 ≤ |f d - g d| := abs_nonneg _
        have hwn : 0 ≤ |w d| := abs_nonneg _
        nlinarith
    _ = E * ((M : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/-- **The choice of `M`.** `⌊Y⌋₊ ≤ (⌊√Y⌋₊ + 1)²`.

The `+ 1` is not slack: with `M = ⌊√Y⌋₊` the inequality is false, as `Y = 10`
shows, where `⌊√10⌋₊² = 9 < 10 = ⌊Y⌋₊`. -/
theorem floor_le_sq_succ {Y : ℝ} (hY : 0 ≤ Y) :
    ⌊Y⌋₊ ≤ (⌊Real.sqrt Y⌋₊ + 1) ^ 2 := by
  have hs : Real.sqrt Y < (⌊Real.sqrt Y⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.sqrt Y)
  have hsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hsnn : (0 : ℝ) ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hYlt : Y < ((⌊Real.sqrt Y⌋₊ : ℝ) + 1) ^ 2 := by nlinarith
  have hfl : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY
  have hcast : (((⌊Real.sqrt Y⌋₊ + 1) ^ 2 : ℕ) : ℝ)
      = ((⌊Real.sqrt Y⌋₊ : ℝ) + 1) ^ 2 := by push_cast; ring
  have : ((⌊Y⌋₊ : ℕ) : ℝ) < (((⌊Real.sqrt Y⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
    rw [hcast]; linarith
  exact le_of_lt (by exact_mod_cast this)

/-- **The size of the `d`-range.** `M + 1 ≤ √Y + 2` for `M = ⌊√Y⌋₊ + 1`.

No hypothesis on `Y` is needed: `Real.sqrt_nonneg` holds unconditionally, so the
floor bound does too. -/
theorem range_size_le (Y : ℝ) :
    ((⌊Real.sqrt Y⌋₊ + 1 : ℕ) : ℝ) + 1 ≤ Real.sqrt Y + 2 := by
  have hfl : ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) ≤ Real.sqrt Y :=
    Nat.floor_le (Real.sqrt_nonneg Y)
  push_cast
  linarith

/-- The per-`d` main term: `(⌊Y⌋₊ / d²) / 24` on the `d` coprime to `6`, and `0`
elsewhere.

The guard is **required**, not cosmetic. `fibre_approx` only bounds the fibre for
`d` coprime to `6`; for other `d` the fibre is empty
(`fibre_empty_of_not_coprime`) while `(⌊Y⌋₊ / d²) / 24` is large, so comparing
against the unguarded expression is false for every even `d`. It also disposes of
`d = 0`, which is not coprime to `6` since `2 ∣ 0`. -/
noncomputable def mainTerm (Y : ℝ) (d : ℕ) : ℝ :=
  open Classical in
  if ¬ (2 ∣ d) ∧ ¬ (3 ∣ d) then ((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) / 24 else 0

/-- **The per-`d` bound, for every `d`.** The fibre over `d` differs from
`mainTerm Y d` by at most `2`, with no coprimality hypothesis: on the coprime `d`
this is `fibre_approx`, and off them both sides vanish. -/
theorem fibre_sub_mainTerm_le (Y : ℝ) (d : ℕ) :
    |((((Finset.Icc 2 ⌊Y⌋₊).filter fun N => N % 24 = 23).filter
        fun N => d ^ 2 ∣ N).card : ℝ) - mainTerm Y d| ≤ 2 := by
  classical
  unfold mainTerm
  by_cases hcop : ¬ (2 ∣ d) ∧ ¬ (3 ∣ d)
  · obtain ⟨h2, h3⟩ := hcop
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (dvd_zero 2) h2
      · exact h
    rw [ite_eq_left ⟨h2, h3⟩]
    exact fibre_approx hd h2 h3
  · -- not coprime: the fibre is empty and the main term is `0`
    rw [ite_eq_right hcop]
    have hor : 2 ∣ d ∨ 3 ∣ d := by
      by_cases h2 : 2 ∣ d
      · exact Or.inl h2
      · exact Or.inr (by tauto)
    rw [fibre_empty_of_not_coprime hor]
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, abs_zero]
    norm_num

/-- **The count against its main sum.** For `Y ≥ 0`,

`|#D(Y) - ∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTerm Y d| ≤ 2 (√Y + 2)`. -/
theorem card_admissible_sub_mainSum_le {Y : ℝ} (hY : 0 ≤ Y) :
    |((admissible Y).card : ℝ)
      - ∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTerm Y d|
      ≤ 2 * (Real.sqrt Y + 2) := by
  classical
  set M : ℕ := ⌊Real.sqrt Y⌋₊ + 1 with hM
  have hMsq : ⌊Y⌋₊ ≤ M ^ 2 := by rw [hM]; exact floor_le_sq_succ hY
  rw [card_admissible_eq_swapped Y hMsq]
  have hagg := sum_weighted_error_le (M := M) (E := 2)
    (f := fun d => ((((Finset.Icc 2 ⌊Y⌋₊).filter fun N => N % 24 = 23).filter
        fun N => d ^ 2 ∣ N).card : ℝ))
    (g := mainTerm Y) (w := fun d => (μ d : ℝ))
    (fun d _ => fibre_sub_mainTerm_le Y d)
    (fun d => PartitionZheng.abs_moebius_le_one d)
  have hrange : ((M : ℕ) : ℝ) + 1 ≤ Real.sqrt Y + 2 := by
    rw [hM]; exact range_size_le Y
  have hstep : (2 : ℝ) * (((M : ℕ) : ℝ) + 1) ≤ 2 * (Real.sqrt Y + 2) := by linarith
  exact le_trans hagg hstep

/-- **Replacing `⌊Y⌋₊` and `ℕ`-division by `Y` and real division.** For `d ≥ 1`
and `Y ≥ 0`, `|(⌊Y⌋₊ / d² : ℕ) - Y / d²| ≤ 2`.

Two roundings are absorbed at once: `⌊Y⌋₊` loses less than `1` against `Y`, and
truncating `ℕ`-division loses less than `d²`, which is `1` after dividing. Their
sum is `(1 + d²)/d² = 1/d² + 1 ≤ 2`. -/
theorem floorDiv_sub_div_le {Y : ℝ} (hY : 0 ≤ Y) {d : ℕ} (hd : 1 ≤ d) :
    |((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) - Y / (d : ℝ) ^ 2| ≤ 2 := by
  have hq : 0 < d ^ 2 := pow_pos hd 2
  have hqR : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hqR0 : (0 : ℝ) < (d : ℝ) ^ 2 := by linarith
  -- `⌊Y⌋₊ = d² * Q + R` with `0 ≤ R < d²`
  set K : ℕ := ⌊Y⌋₊ with hK
  set Q : ℕ := K / d ^ 2 with hQ
  set R : ℕ := K % d ^ 2 with hR
  have hdm : d ^ 2 * Q + R = K := Nat.div_add_mod K (d ^ 2)
  have hRlt : R < d ^ 2 := Nat.mod_lt K hq
  have hfl : (K : ℝ) ≤ Y := Nat.floor_le hY
  have hlt : Y < (K : ℝ) + 1 := Nat.lt_floor_add_one Y
  -- cast the division identity
  have hdmR : (d : ℝ) ^ 2 * (Q : ℝ) + (R : ℝ) = (K : ℝ) := by
    have : ((d ^ 2 * Q + R : ℕ) : ℝ) = ((K : ℕ) : ℝ) := by exact_mod_cast hdm
    push_cast at this
    linarith
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have hRltR : (R : ℝ) < (d : ℝ) ^ 2 := by exact_mod_cast hRlt
  -- `Q ≤ Y/d² ≤ Q + 2`
  have hA : (Q : ℝ) ≤ Y / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ hqR0]; nlinarith
  have hB : Y / (d : ℝ) ^ 2 ≤ (Q : ℝ) + 2 := by
    rw [div_le_iff₀ hqR0]; nlinarith
  rw [abs_le]
  constructor <;> linarith

/-! ### The restricted Möbius series and its partial sums -/

/-- Coprimality to `6` is the conjunction of the two divisibility conditions. -/
theorem coprime_six_iff (d : ℕ) : Nat.Coprime d 6 ↔ ¬ (2 ∣ d) ∧ ¬ (3 ∣ d) := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, Nat.coprime_mul_iff_right]
  constructor
  · intro h
    exact ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h.1.symm,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h.2.symm⟩
  · intro h
    exact ⟨((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h.1).symm,
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h.2).symm⟩

/-- The Möbius summand `μ(d)/d²`, extended by `0` off the `d` coprime to `6`.

This is `coprimeSummand` transported from the subtype `{m // Nat.Coprime m 6}`
to all of `ℕ`. -/
noncomputable def coprimeTerm (d : ℕ) : ℝ :=
  if Nat.Coprime d 6 then (μ d : ℝ) / (d : ℝ) ^ 2 else 0

/-- `|μ(d)/d²| ≤ 1/d²`, uniformly in `d`. At `d = 0` both sides are `0`: `0` is
not coprime to `6`, and `(0 : ℝ)⁻¹ = 0`. -/
theorem abs_coprimeTerm_le (d : ℕ) : |coprimeTerm d| ≤ ((d : ℝ) ^ 2)⁻¹ := by
  unfold coprimeTerm
  by_cases h : Nat.Coprime d 6
  · rw [ite_eq_left h]
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact absurd h (by decide)
      · exact hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hsq : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := abs_moebius_le_one d
    rw [abs_div, abs_of_pos hsq, ← one_div]
    gcongr
  · rw [ite_eq_right h, abs_zero]
    positivity

/-- `∑ 1/d²` converges, in the inverse form the tail bound uses. -/
theorem summable_inv_sq : Summable (fun d : ℕ => ((d : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun d : ℕ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  simpa only [one_div] using h

/-- The restricted Möbius series is summable, by comparison with `∑ 1/d²`. -/
theorem summable_coprimeTerm : Summable coprimeTerm := by
  refine summable_inv_sq.of_norm_bounded ?_
  intro d
  rw [Real.norm_eq_abs]
  exact abs_coprimeTerm_le d

/-- **The value of the restricted series.** `∑_d coprimeTerm d = 9/π²`.

This is `coprime_moebius_tsum` with the subtype index `{m // Nat.Coprime m 6}`
replaced by all of `ℕ`. The reindexing is legal because `coprimeTerm` is
supported on the coprime `d` by construction. -/
theorem coprimeTerm_tsum : ∑' d : ℕ, coprimeTerm d = 9 / Real.pi ^ 2 := by
  have hsupp : Function.support coprimeTerm
      ⊆ Set.range (Subtype.val : {m : ℕ // Nat.Coprime m 6} → ℕ) := by
    intro d hd
    have h : Nat.Coprime d 6 := by
      by_contra hc
      exact hd (by unfold coprimeTerm; rw [ite_eq_right hc])
    exact ⟨⟨d, h⟩, rfl⟩
  rw [← Subtype.val_injective.tsum_eq hsupp, ← coprime_moebius_tsum]
  refine tsum_congr fun m => ?_
  unfold coprimeTerm coprimeSummand
  rw [ite_eq_left m.2]

/-- **The tail of a series dominated by `1/d²`.** Past the index `M` such a
series contributes at most `2/(M+1)`.

No separate convergence argument for the tail is needed: `summable_inv_sq`
dominates the shifted series termwise. -/
theorem abs_tsum_nat_add_le {f : ℕ → ℝ} (hf : Summable f)
    (hbd : ∀ d, |f d| ≤ ((d : ℝ) ^ 2)⁻¹) (M : ℕ) :
    |∑' i : ℕ, f (i + (M + 1))| ≤ 2 / ((M : ℝ) + 1) := by
  have habs : Summable (fun i : ℕ => |f (i + (M + 1))|) :=
    summable_abs_iff.mpr ((summable_nat_add_iff (M + 1)).mpr hf)
  have h1 : |∑' i : ℕ, f (i + (M + 1))| ≤ ∑' i : ℕ, |f (i + (M + 1))| := by
    have hnorm : Summable fun i : ℕ => ‖f (i + (M + 1))‖ := by
      simpa only [Real.norm_eq_abs] using habs
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  have h2 : ∑' i : ℕ, |f (i + (M + 1))| ≤ 2 / ((M : ℝ) + 1) := by
    refine Real.tsum_le_of_sum_range_le (fun i => abs_nonneg _) fun n => ?_
    have hio : Finset.Ico (M + 1) (M + 1 + n) = Finset.Ioo M (M + 1 + n) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_Ioo]
      omega
    have hre : ∑ j ∈ Finset.Ico (M + 1) (M + 1 + n), (((j : ℕ) : ℝ) ^ 2)⁻¹
        = ∑ i ∈ Finset.range n, (((i + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
    calc ∑ i ∈ Finset.range n, |f (i + (M + 1))|
        ≤ ∑ i ∈ Finset.range n, (((i + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum fun i _ => hbd _
      _ = ∑ j ∈ Finset.Ioo M (M + 1 + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by rw [← hio, hre]
      _ ≤ 2 / ((M : ℝ) + 1) := sum_Ioo_inv_sq_le M (M + 1 + n)
  linarith

/-- **The partial restricted series against its value.** For every `M`,

`|∑_{d ≤ M} coprimeTerm d - 9/π²| ≤ 2/(M+1)`,

an explicit error rather than an `O(1/M)`. -/
theorem abs_coprimeTerm_range_sub_le (M : ℕ) :
    |∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2|
      ≤ 2 / ((M : ℝ) + 1) := by
  have hsplit := summable_coprimeTerm.sum_add_tsum_nat_add (M + 1)
  rw [coprimeTerm_tsum] at hsplit
  have hkey : ∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2
      = -(∑' i : ℕ, coprimeTerm (i + (M + 1))) := by linarith
  rw [hkey, abs_neg]
  exact abs_tsum_nat_add_le summable_coprimeTerm abs_coprimeTerm_le M

/-! ### From the main sum to `δY` -/

/-- The per-`d` main term with both roundings removed: `Y` in place of `⌊Y⌋₊`,
and real division in place of `ℕ`-division.

The coprimality guard is retained for the same reason as in `mainTerm`: off the
`d` coprime to `6` the fibre is empty while `Y/(24d²)` is large. -/
noncomputable def mainTermReal (Y : ℝ) (d : ℕ) : ℝ :=
  if Nat.Coprime d 6 then Y / (d : ℝ) ^ 2 / 24 else 0

/-- **The per-`d` cost of removing the roundings**, namely `2/24 = 1/12`.

On the `d` coprime to `6` this is `floorDiv_sub_div_le` divided by `24`, and off
them both sides vanish. -/
theorem mainTerm_sub_mainTermReal_le {Y : ℝ} (hY : 0 ≤ Y) (d : ℕ) :
    |mainTerm Y d - mainTermReal Y d| ≤ 1 / 12 := by
  unfold mainTerm mainTermReal
  by_cases h : Nat.Coprime d 6
  · obtain ⟨h2, h3⟩ := (coprime_six_iff d).mp h
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact absurd (dvd_zero 2) h2
      · exact hd
    rw [ite_eq_left ⟨h2, h3⟩, ite_eq_left h]
    have hkey := floorDiv_sub_div_le hY hd
    have hrw : ((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) / 24 - Y / (d : ℝ) ^ 2 / 24
        = (((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) - Y / (d : ℝ) ^ 2) / 24 := by ring
    rw [hrw, abs_div, show |(24 : ℝ)| = 24 from by norm_num]
    linarith
  · have hnc : ¬ (¬ (2 ∣ d) ∧ ¬ (3 ∣ d)) := fun hc => h ((coprime_six_iff d).mpr hc)
    rw [ite_eq_right hnc, ite_eq_right h, sub_zero, abs_zero]
    norm_num

/-- **The main sum with the roundings removed.** For `Y ≥ 0`,

`|∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTerm Y d - ∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTermReal Y d|
  ≤ (1/12)(√Y + 2)`. -/
theorem mainSum_sub_realSum_le {Y : ℝ} (hY : 0 ≤ Y) :
    |∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTerm Y d
      - ∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTermReal Y d|
      ≤ 1 / 12 * (Real.sqrt Y + 2) := by
  set M : ℕ := ⌊Real.sqrt Y⌋₊ + 1 with hM
  have hagg := sum_weighted_error_le (M := M) (E := 1 / 12)
    (f := mainTerm Y) (g := mainTermReal Y) (w := fun d => (μ d : ℝ))
    (fun d _ => mainTerm_sub_mainTermReal_le hY d)
    (fun d => PartitionZheng.abs_moebius_le_one d)
  have hrange : ((M : ℕ) : ℝ) + 1 ≤ Real.sqrt Y + 2 := by
    rw [hM]; exact range_size_le Y
  have hstep : (1 : ℝ) / 12 * (((M : ℕ) : ℝ) + 1) ≤ 1 / 12 * (Real.sqrt Y + 2) := by
    linarith
  exact le_trans hagg hstep

/-- **The rounding-free main sum, factored.** `μ(d) · mainTermReal Y d` is
`(Y/24) · coprimeTerm d`, so the sum is `(Y/24)` times a partial sum of the
restricted Möbius series. -/
theorem realSum_eq (Y : ℝ) (M : ℕ) :
    ∑ d ∈ Finset.range (M + 1), (μ d : ℝ) * mainTermReal Y d
      = Y / 24 * ∑ d ∈ Finset.range (M + 1), coprimeTerm d := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold mainTermReal coprimeTerm
  by_cases h : Nat.Coprime d 6
  · rw [ite_eq_left h, ite_eq_left h]; ring
  · rw [ite_eq_right h, ite_eq_right h]; ring

/-- **The rounding-free main sum against `δY`.** For `Y ≥ 1`,

`|∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTermReal Y d - δY| ≤ √Y/12`.

The constants close exactly, with nothing absorbed into the error: the partial
sum `S_M` lies within `2/(M+1) ≤ 2/√Y` of `9/π²`, and `(Y/24)(2/√Y) = √Y/12`. -/
theorem realSum_sub_delta_le {Y : ℝ} (hY : 1 ≤ Y) :
    |∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTermReal Y d
      - delta * Y| ≤ Real.sqrt Y / 12 := by
  set M : ℕ := ⌊Real.sqrt Y⌋₊ + 1 with hM
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt Y := by
    have h : Real.sqrt 1 ≤ Real.sqrt Y := Real.sqrt_le_sqrt hY
    rwa [Real.sqrt_one] at h
  have hs0 : (0 : ℝ) < Real.sqrt Y := by linarith
  have hsq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0
  have hdelta : delta * Y = Y / 24 * (9 / Real.pi ^ 2) := by rw [delta_eq]; ring
  rw [realSum_eq, hdelta]
  -- the truncation error, transported to the `√Y` scale
  have hfl : Real.sqrt Y < ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMR : Real.sqrt Y ≤ ((M : ℕ) : ℝ) + 1 := by
    rw [hM]; push_cast; linarith
  have hdiv : 2 / (((M : ℕ) : ℝ) + 1) ≤ 2 / Real.sqrt Y := by
    gcongr
  have hbound : |∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2|
      ≤ 2 / Real.sqrt Y := le_trans (abs_coprimeTerm_range_sub_le M) hdiv
  have hfac : Y / 24 * ∑ d ∈ Finset.range (M + 1), coprimeTerm d
      - Y / 24 * (9 / Real.pi ^ 2)
      = Y / 24 * (∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2) := by
    ring
  have hkey : Y / 24 * (2 / Real.sqrt Y) = Real.sqrt Y / 12 := by
    have hne : Real.sqrt Y ≠ 0 := ne_of_gt hs0
    field_simp
    nlinarith [hsq]
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y / 24)]
  calc Y / 24 * |∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2|
      ≤ Y / 24 * (2 / Real.sqrt Y) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
    _ = Real.sqrt Y / 12 := hkey

/-- **`lem_Dset_card`.** `|#D(Y) - δY| ≤ 7√Y` for every `Y ≥ 1`, with
`δ = 3/(8π²)`.

The constant is existentially quantified rather than hidden in `O()`-notation,
and the proof exhibits `C = 7`.

The three errors that make up `C`, all for `Y ≥ 1`, where `√Y ≥ 1`:

* `2(√Y + 2) ≤ 6√Y` from `card_admissible_sub_mainSum_le`, the residue count in
  each fibre;
* `(1/12)(√Y + 2) ≤ (1/4)√Y` from `mainSum_sub_realSum_le`, the two roundings;
* `√Y/12` from `realSum_sub_delta_le`, the truncation of the Möbius series.

Their sum is at most `(19/3)√Y`, and `19/3 < 7`. -/
@[pz_tag "lem_Dset_card"]
theorem card_admissible_sub_delta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y := by
  refine ⟨7, by norm_num, fun Y hY => ?_⟩
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt Y := by
    have h : Real.sqrt 1 ≤ Real.sqrt Y := Real.sqrt_le_sqrt hY
    rwa [Real.sqrt_one] at h
  have h1 := card_admissible_sub_mainSum_le hY0
  have h2 := mainSum_sub_realSum_le hY0
  have h3 := realSum_sub_delta_le hY
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end PartitionZheng
