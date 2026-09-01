/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import PartitionZheng.Constants
public import PartitionZheng.Discriminants
public import PartitionZheng.Forms
public import PartitionZheng.Integrals
public import PartitionZheng.Weight

/-!
# The class-number average

The total class number of the admissible discriminants up to `Y` is at most
`(beta + ε) Y^{3/2}` for every `ε > 0` once `Y` is large, where
`beta = π / 108`.

The passage from class numbers to a lattice count is the content of this file.
Every reduced form of discriminant `-D` is a reduced triple, and for distinct
`D` those triple sets are disjoint — the discriminant `4ac - b²` separates
them — so the total class number is at most the number of triples in
`reducedTriplesUpTo Y`. Fibring that set over its first coefficient `a`, which
reducedness confines to `1 ≤ a ≤ sqrt (Y / 3)`, turns the count into a sum over
`a` of the per-`a` counts, which is what the lattice-point estimate bounds.

The two error sums are handled here: `∑_{a ≤ sqrt (Y/3)} 1/a` by Mathlib's
harmonic bound, and `∑_{a ≤ sqrt (Y/3)} a` by bounding every term by the number
of terms. Both are absorbed into `Y (1 + log Y)`, and
`Y (1 + log Y) ≤ ε Y^{3/2}` for large `Y` is proved by writing `Y = v⁴` with
`v` the fourth root, so that `log Y = 4 log v ≤ 4 v` reduces the claim to a
polynomial inequality in `v`.

Following the convention of `PartitionZheng.ZH`, `Y ^ (3/2)` is written
`Y * sqrt Y`, which agrees with it on the range `Y ≥ 0` where it is used and
avoids `rpow`.

## Main results

* `PartitionZheng.reducedTriplesUpTo_finite` — the lattice set is finite.
* `PartitionZheng.sum_classNumber_le_ncard` — the total class number is at most
  `#T*(Y)`.
* `PartitionZheng.ncard_reducedTriplesUpTo_le_sum` — fibring `T*(Y)` over `a`.
* `PartitionZheng.class_average` — the class-number average.
-/

@[expose] public section

namespace PartitionZheng

/-! ### The lattice set and its fibres -/

/-- Membership in `reducedTriplesUpTo` spelled out on an explicit triple. The
ascription is what beta-reduces the projections `(a, b, c).2.1`, without which
`omega` treats them as atoms distinct from `b`. -/
theorem mem_reducedTriplesUpTo {Y : ℝ} {a b c : ℤ} :
    (a, b, c) ∈ reducedTriplesUpTo Y ↔
      |b| ≤ a ∧ a ≤ c ∧ 0 < 4 * a * c - b ^ 2 ∧
        ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y ∧ (4 * a * c - b ^ 2) % 24 = 23 :=
  Iff.rfl

/-- Reducedness confines the first coefficient of a triple of discriminant at
most `Y` to `1 ≤ a ≤ sqrt (Y / 3)`. -/
theorem reducedTriplesUpTo_fst_bounds {Y : ℝ} {p : ℤ × ℤ × ℤ} (hp : p ∈ reducedTriplesUpTo Y) :
    1 ≤ p.1 ∧ (p.1 : ℝ) ≤ Real.sqrt (Y / 3) := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨hb, hac, hpos, hle, -⟩ := mem_reducedTriplesUpTo.mp hp
  refine ⟨one_le_a_of_mem hpos ⟨hb, hac, rfl⟩, ?_⟩
  have h := three_sq_le_of_disc_le hb hac hle
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- The triples of discriminant at most `Y` form a finite set: the discriminant
`D = 4ac - b²` satisfies `0 < D ≤ ⌊Y⌋`, and `3a² ≤ D` with `|b| ≤ a ≤ c` bounds
all three coefficients by `D`. -/
theorem reducedTriplesUpTo_finite (Y : ℝ) : (reducedTriplesUpTo Y).Finite := by
  have hfin : (Set.Icc (-⌊Y⌋) ⌊Y⌋ ×ˢ
      (Set.Icc (-⌊Y⌋) ⌊Y⌋ ×ˢ Set.Icc (-⌊Y⌋) ⌊Y⌋)).Finite :=
    (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  refine hfin.subset ?_
  rintro ⟨a, b, c⟩ hp
  obtain ⟨hb, hac, hpos, hle, -⟩ := mem_reducedTriplesUpTo.mp hp
  have hDN : 4 * a * c - b ^ 2 ≤ ⌊Y⌋ := Int.le_floor.mpr hle
  have ha1 : 1 ≤ a := one_le_a_of_mem hpos ⟨hb, hac, rfl⟩
  have h3 : 3 * a ^ 2 ≤ 4 * a * c - b ^ 2 := three_sq_le_disc hb hac
  have hbsq : b ^ 2 ≤ a ^ 2 := by
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
  have haa : a ≤ a ^ 2 := by nlinarith
  have haN : a ≤ ⌊Y⌋ := by nlinarith
  have hcN : c ≤ ⌊Y⌋ := by nlinarith
  have hbl : -⌊Y⌋ ≤ b := by
    have := neg_le_of_abs_le hb
    omega
  have hbu : b ≤ ⌊Y⌋ := le_trans (le_of_abs_le hb) haN
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

/-- For an admissible `D ≤ Y`, every reduced triple of discriminant `-D` is a
triple of discriminant at most `Y` in the admissible congruence class. -/
theorem reducedTriples_subset_upTo {Y : ℝ} (hY : 0 ≤ Y) {D : ℕ} (hD : D ∈ admissible Y) :
    reducedTriples (D : ℤ) ⊆ reducedTriplesUpTo Y := by
  obtain ⟨⟨hD2, hDY⟩, hmod, -⟩ := mem_admissible.mp hD
  rintro ⟨a, b, c⟩ ⟨hb, hac, hdisc⟩
  refine ⟨hb, hac, ?_, ?_, ?_⟩
  · rw [hdisc]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hD2
  · rw [hdisc]
    have h1 : (D : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hDY
    have h2 : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY
    push_cast
    linarith
  · rw [hdisc]; omega

/-- Dropping the class-number normalisations and collecting the triple sets of
all admissible `D ≤ Y`: the total class number is at most `#T*(Y)`. The sets
`T(D)` are disjoint for distinct `D`, being separated by `4ac - b²`. -/
theorem sum_classNumber_le_ncard {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ D ∈ admissible Y, classNumber (D : ℤ) ≤ (reducedTriplesUpTo Y).ncard := by
  classical
  have hfin := reducedTriplesUpTo_finite Y
  set t : ℕ → Finset (ℤ × ℤ × ℤ) :=
    fun D => hfin.toFinset.filter fun p => 4 * p.1 * p.2.2 - p.2.1 ^ 2 = (D : ℤ) with htdef
  have hcoe : ∀ D ∈ admissible Y, (↑(t D) : Set (ℤ × ℤ × ℤ)) = reducedTriples (D : ℤ) := by
    intro D hD
    ext p
    obtain ⟨a, b, c⟩ := p
    simp only [htdef, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hb, hac, -, -, -⟩, hdisc⟩
      exact ⟨hb, hac, hdisc⟩
    · intro hmem
      exact ⟨reducedTriples_subset_upTo hY hD hmem, hmem.2.2⟩
  have hdisj : (↑(admissible Y) : Set ℕ).PairwiseDisjoint t := by
    intro D _ D' _ hne
    simp only [Function.onFun]
    refine Finset.disjoint_left.mpr ?_
    intro p hp hp'
    simp only [htdef, Finset.mem_filter] at hp hp'
    exact hne (by exact_mod_cast hp.2.symm.trans hp'.2)
  have hsub : (admissible Y).biUnion t ⊆ hfin.toFinset := by
    refine Finset.biUnion_subset.mpr fun D _ => ?_
    simp only [htdef]
    exact Finset.filter_subset _ _
  calc ∑ D ∈ admissible Y, classNumber (D : ℤ)
      ≤ ∑ D ∈ admissible Y, (reducedTriples (D : ℤ)).ncard := by
        refine Finset.sum_le_sum fun D hD => ?_
        have hD2 := (mem_admissible.mp hD).1.1
        exact classNumber_le (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hD2)
    _ = ∑ D ∈ admissible Y, (t D).card := by
        refine Finset.sum_congr rfl fun D hD => ?_
        rw [← hcoe D hD, Set.ncard_coe_finset]
    _ = ((admissible Y).biUnion t).card := (Finset.card_biUnion hdisj).symm
    _ ≤ hfin.toFinset.card := Finset.card_le_card hsub
    _ = (reducedTriplesUpTo Y).ncard := by
        rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]

/-- Fibring the triples of discriminant at most `Y` over their first
coefficient, which `reducedTriplesUpTo_fst_bounds` confines to `1 ≤ a ≤ sqrt (Y / 3)`. -/
theorem ncard_reducedTriplesUpTo_le_sum (Y : ℝ) :
    (reducedTriplesUpTo Y).ncard
      ≤ ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
          {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard := by
  classical
  have hfin := reducedTriplesUpTo_finite Y
  have hcard : (reducedTriplesUpTo Y).ncard = hfin.toFinset.card := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  have hmapsto : Set.MapsTo (fun p : ℤ × ℤ × ℤ => p.1.toNat)
      ↑hfin.toFinset ↑(Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊) := by
    intro p hp
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hp
    obtain ⟨ha1, ha2⟩ := reducedTriplesUpTo_fst_bounds hp
    have h0 : (0 : ℤ) ≤ p.1 := by omega
    have hcast : ((p.1.toNat : ℕ) : ℝ) = (p.1 : ℝ) := by
      rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg h0]
    have hlow : 1 ≤ p.1.toNat := by omega
    have hhigh : p.1.toNat ≤ ⌊Real.sqrt (Y / 3)⌋₊ :=
      Nat.le_floor (by rw [hcast]; exact ha2)
    simpa [Finset.mem_Icc] using And.intro hlow hhigh
  rw [hcard, Finset.card_eq_sum_card_fiberwise hmapsto]
  refine Finset.sum_le_sum fun a ha => ?_
  have hfibfin : {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.Finite := by
    have hpre : {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}
        = (fun q : ℤ × ℤ => ((a : ℤ), q.1, q.2)) ⁻¹' reducedTriplesUpTo Y := rfl
    rw [hpre]
    refine Set.Finite.preimage ?_ hfin
    intro x _ y _ h
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext_iff.mpr h
  have hinj : Set.InjOn Prod.snd
      (↑({p ∈ hfin.toFinset | p.1.toNat = a}) : Set (ℤ × ℤ × ℤ)) := by
    intro p hp q hq h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hp hq
    have hp1 := (reducedTriplesUpTo_fst_bounds hp.1).1
    have hq1 := (reducedTriplesUpTo_fst_bounds hq.1).1
    have hfsteq := hp.2.trans hq.2.symm
    exact Prod.ext_iff.mpr ⟨by omega, h⟩
  calc ({p ∈ hfin.toFinset | p.1.toNat = a}).card
      = (({p ∈ hfin.toFinset | p.1.toNat = a}).image Prod.snd).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard := by
        rw [← Set.ncard_coe_finset]
        refine Set.ncard_le_ncard ?_ hfibfin
        intro q hq
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
          Set.Finite.mem_toFinset] at hq
        obtain ⟨p, ⟨hpS, hpa⟩, rfl⟩ := hq
        have hp1 := (reducedTriplesUpTo_fst_bounds hpS).1
        have hfst : ((a : ℤ)) = p.1 := by omega
        rw [hfst]
        exact hpS

/-! ### The error sums -/

/-- The harmonic sum over `1 ≤ a ≤ y`, from Mathlib's bound on the harmonic
numbers. -/
theorem sum_inv_le_one_add_log {y : ℝ} (hy : 1 ≤ y) :
    ∑ a ∈ Finset.Icc 1 ⌊y⌋₊, ((a : ℝ))⁻¹ ≤ 1 + Real.log y := by
  have h := harmonic_floor_le_one_add_log y hy
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- The sum of `a` over `1 ≤ a ≤ sqrt (Y / 3)` is at most `Y / 3`, by bounding
every term by the number of terms. -/
theorem sum_natCast_le_div_three {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ) ≤ Y / 3 := by
  have hN : ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (Y / 3) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hsq : Real.sqrt (Y / 3) ^ 2 = Y / 3 := Real.sq_sqrt (by linarith)
  have hterm : ∀ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
      (a : ℝ) ≤ ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) :=
    fun a ha => Nat.cast_le.mpr (Finset.mem_Icc.mp ha).2
  calc ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ)
      ≤ (Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊).card •
          ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) * ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) := by
        simp [Nat.card_Icc]
    _ ≤ Y / 3 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌊Real.sqrt (Y / 3)⌋₊]

/-- The two error sums of the lattice count, absorbed into `Y (1 + log Y)`. -/
theorem sum_triple_error_le {Y C : ℝ} (hY : 3 ≤ Y) (hC : 0 < C) :
    ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, C * (Y / (a : ℝ) + (a : ℝ))
      ≤ 2 * C * (Y * (1 + Real.log Y)) := by
  have hsplit : ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, C * (Y / (a : ℝ) + (a : ℝ))
      = C * Y * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, ((a : ℝ))⁻¹)
        + C * ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [div_eq_mul_inv]; ring
  have h1 : (1 : ℝ) ≤ Real.sqrt (Y / 3) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hinv := sum_inv_le_one_add_log h1
  have hid := sum_natCast_le_div_three (Y := Y) (by linarith)
  have hlt : Real.sqrt (Y / 3) ≤ Y := by
    have h := Real.sqrt_le_sqrt (show Y / 3 ≤ Y ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ Y)] at h
  have hlogsq : Real.log (Real.sqrt (Y / 3)) ≤ Real.log Y :=
    Real.log_le_log (by linarith) hlt
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hCY : (0 : ℝ) ≤ C * Y := mul_nonneg hC.le (by linarith)
  have hA : C * Y * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, ((a : ℝ))⁻¹)
      ≤ C * Y * (1 + Real.log Y) :=
    mul_le_mul_of_nonneg_left (by linarith) hCY
  have hB : C * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ)) ≤ C * (Y / 3) :=
    mul_le_mul_of_nonneg_left hid hC.le
  have hD : C * (Y / 3) ≤ C * (Y * (1 + Real.log Y)) := by
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Y) hlog0]
  rw [hsplit]
  nlinarith [hA, hB, hD]

/-! ### `Y log Y` is eventually below `ε Y^{3/2}` -/

/-- For every `K, ε > 0` there is a threshold past which
`K Y (1 + log Y) ≤ ε Y^{3/2}`.

Writing `Y = v⁴` with `v` the fourth root of `Y` turns `log Y = 4 log v` and
`log v ≤ v` into the polynomial inequality `K (v⁴ + 4v⁵) ≤ ε v⁶`, which holds
as soon as `v ≥ max 1 (5K/ε)`. -/
theorem exists_mul_log_le {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 3 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      K * (Y * (1 + Real.log Y)) ≤ ε * (Y * Real.sqrt Y) := by
  have hM1 : (1 : ℝ) ≤ max 1 (5 * K / ε) := le_max_left _ _
  have hM2 : 5 * K / ε ≤ max 1 (5 * K / ε) := le_max_right _ _
  refine ⟨max 3 (max 1 (5 * K / ε) ^ 4), le_max_left _ _, fun Y hY => ?_⟩
  have hY3 : 3 ≤ Y := le_trans (le_max_left _ _) hY
  have hYM : max 1 (5 * K / ε) ^ 4 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  obtain ⟨v, hv0, hv2⟩ : ∃ v : ℝ, 0 ≤ v ∧ v ^ 2 = Real.sqrt Y :=
    ⟨Real.sqrt (Real.sqrt Y), Real.sqrt_nonneg _, Real.sq_sqrt hs0⟩
  have hv4 : v ^ 4 = Y := by
    have h : v ^ 4 = (v ^ 2) ^ 2 := by ring
    rw [h, hv2, Real.sq_sqrt hY0.le]
  have hMs : max 1 (5 * K / ε) ^ 2 ≤ Real.sqrt Y :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hvM : max 1 (5 * K / ε) ≤ v := by nlinarith
  have hv1 : (1 : ℝ) ≤ v := le_trans hM1 hvM
  have hlogv : Real.log v ≤ v :=
    le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hlogY : Real.log Y = 4 * Real.log v := by
    rw [← hv4, Real.log_pow]; norm_num
  have hεv : 5 * K ≤ ε * v := by
    have h := le_trans hM2 hvM
    rw [div_le_iff₀ hε] at h
    linarith
  have hv45 : v ^ 4 ≤ v ^ 5 := by
    nlinarith [mul_le_mul_of_nonneg_left hv1 (pow_nonneg hv0 4)]
  have key : K * (v ^ 4 * (1 + 4 * Real.log v)) ≤ ε * (v ^ 4 * v ^ 2) := by
    have h1 : K * (v ^ 4 * (1 + 4 * Real.log v)) ≤ K * (v ^ 4 * (1 + 4 * v)) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogv (mul_nonneg hK.le (pow_nonneg hv0 4))]
    have h2 : K * (v ^ 4 * (1 + 4 * v)) ≤ 5 * K * v ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_left hv45 hK.le]
    have h3 : 5 * K * v ^ 5 ≤ ε * (v ^ 4 * v ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hεv (pow_nonneg hv0 5)]
    linarith
  rw [hlogY, ← hv2, ← hv4]
  exact key

/-! ### The class-number average -/

/-- **The class-number average.** For every `ε > 0` there is a `Y₀ ≥ 2` such
that the total class number of the admissible discriminants up to `Y` is at
most `(beta + ε) Y^{3/2}` for every `Y ≥ Y₀`, where `Y^{3/2}` is written
`Y * sqrt Y` and `beta = π / 108`.

The two hypotheses are the lattice-point estimates the bound rests on:

* `hTriple` counts the pairs `(b, c)` completing a fixed first coefficient `a`
  to a triple of discriminant at most `Y`: their number is
  `weight a / 6 * areaF Y a` up to an error `C * (Y / a + a)`.
* `hSummation` sums the area function `areaF` against the residue weight
  `weight` over `1 ≤ a ≤ sqrt (Y / 3)`: the total is
  `π / 108 * Y^{3/2}` up to an error `C * (Y * log Y)`. -/
@[pz_tag "lem_class_average"]
theorem class_average
    (hTriple : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y → ∀ a : ℤ, 1 ≤ a →
      (a : ℝ) ≤ Real.sqrt (Y / 3) →
      ({q : ℤ × ℤ | (a, q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard : ℝ)
        ≤ (weight a : ℝ) / 6 * areaF Y a + C * (Y / (a : ℝ) + (a : ℝ)))
    (hSummation : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight a : ℝ) / 6 * areaF Y a
        ≤ Real.pi / 108 * (Y * Real.sqrt Y) + C * (Y * Real.log Y)) :
    ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y) := by
  obtain ⟨C₁, hC₁, hT⟩ := hTriple
  obtain ⟨C₂, hC₂, hS⟩ := hSummation
  intro ε hε
  obtain ⟨Y₁, hY₁, hbound⟩ :=
    exists_mul_log_le (K := 2 * C₁ + C₂) (ε := ε) (by linarith) hε
  refine ⟨max 3 Y₁, le_trans (by norm_num) (le_max_left _ _), fun Y hY => ?_⟩
  have hY3 : 3 ≤ Y := le_trans (le_max_left _ _) hY
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have step1 : ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ)
      ≤ ((reducedTriplesUpTo Y).ncard : ℝ) := by
    exact_mod_cast sum_classNumber_le_ncard (Y := Y) hY0
  have step2 : ((reducedTriplesUpTo Y).ncard : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
          ({q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard : ℝ) := by
    exact_mod_cast ncard_reducedTriplesUpTo_le_sum Y
  have step3 : ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
        ({q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard : ℝ)
      ≤ (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight a : ℝ) / 6 * areaF Y a)
        + ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, C₁ * (Y / (a : ℝ) + (a : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    have haR : ((a : ℤ) : ℝ) ≤ Real.sqrt (Y / 3) := by
      have h : ((a : ℕ) : ℝ) ≤ Real.sqrt (Y / 3) := by
        rw [← Nat.le_floor_iff (Real.sqrt_nonneg _)]
        exact ha2
      exact_mod_cast h
    have h := hT Y (by linarith) (a : ℤ) (by exact_mod_cast ha1) haR
    push_cast at h ⊢
    exact h
  have step4 := hS Y (by linarith)
  have step5 := sum_triple_error_le (Y := Y) (C := C₁) hY3 hC₁
  have step6 := hbound Y (le_trans (le_max_right _ _) hY)
  have herr : C₂ * (Y * Real.log Y) ≤ C₂ * (Y * (1 + Real.log Y)) := by
    nlinarith [mul_nonneg hC₂.le hY0]
  have hbeta : beta = Real.pi / 108 := rfl
  rw [hbeta]
  linarith [step1, step2, step3, step4, step5, step6, herr]

end PartitionZheng
