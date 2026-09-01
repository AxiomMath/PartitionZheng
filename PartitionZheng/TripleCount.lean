/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.Congruence
public import PartitionZheng.FIntegral
public import PartitionZheng.Forms
public import PartitionZheng.LatticeCount

/-!
# Counting reduced triples with a given first coefficient

For a fixed inner coefficient `a`, the reduced triples of discriminant at most
`Y` in the admissible congruence class are counted by their remaining two
coefficients. The count is `w(a)/6 · F_Y(a) + O(Y/a + a)`, with the constant
exhibited: `18`. No asymptotic notation appears, since the summation over `a`
needs the constant uniform in both `Y` and `a`.

`card_c_le` bounds the outer coefficients for fixed `a` and `b` by
`#(bClasses a b) · L⁺(b)/6 + #(bClasses a b)` where `L⁺(t) = (Y + t² - 4a²)₊/(4a)`;
`sum_bClasses_split` groups the sum over `b` into the two class counts;
`weight_cast` recognises `2·#(cClasses a 0) + #(cClasses a 2)` as `w(a)`; and
`integral_Lplus_eq` converts the integral of `L⁺` into `6 F_Y(a)`.

The sum-to-integral comparison is one-sided and only ever needs an upper bound,
so each of the three odd residue classes modulo `6` is handled by
`sum_class_le`: split `[-a, a]` at `0`, reflect the negative half through the
evenness of `L⁺`, and on each monotone half drop the largest point of the
progression — which costs one boundary term `L⁺(a) ≤ Y/(4a)` — so that the
remaining points have their whole step-`6` block inside the interval and
`sum_step_six_le_integral` applies.

The constants close exactly. Each class contributes `(1/6)∫_0^a L⁺ = F_Y(a)/2`
per half, hence `F_Y(a)` per class; the classes `b ≡ 1, 5` carry
`#(cClasses a 0)` and `b ≡ 3` carries `#(cClasses a 2)`; and the `1/6` of
`card_c_le` survives. The main term is therefore
`(2·#(cClasses a 0) + #(cClasses a 2))/6 · F_Y(a) = w(a)/6 · F_Y(a)`, with
nothing left over to hide in the error.

## Main results

* `PartitionZheng.integral_Lplus_half` — `∫_0^a L⁺ = 3 F_Y(a)`.
* `PartitionZheng.sum_progression_le` — the step-`6` comparison on `[0, a]`.
* `PartitionZheng.sum_class_le` — one residue class modulo `6` over `[-a, a]`.
* `PartitionZheng.card_fibre_le` — the pairs with a fixed middle coefficient.
* `PartitionZheng.card_pairs_le` — the pair count, for a `Finset` of pairs.
* `PartitionZheng.exists_const_card_pairs_le` — the pair count with an explicit
  constant, for the triples of `reducedTriplesUpTo Y`.
-/

@[expose] public section

namespace PartitionZheng

open Finset

/-- `L⁺` is a polynomial composed with `max` and divided by a constant, hence
continuous. -/
theorem Lplus_continuous (Y a : ℝ) : Continuous (Lplus Y a) := by
  unfold Lplus
  fun_prop

/-- `L⁺` is interval integrable on every interval, being continuous. -/
theorem Lplus_intervalIntegrable (Y a u v : ℝ) :
    IntervalIntegrable (Lplus Y a) MeasureTheory.volume u v :=
  (Lplus_continuous Y a).intervalIntegrable u v

/-- `L⁺` is nonnegative for `a > 0`: it is a positive part divided by `4a`. -/
theorem Lplus_nonneg {Y a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ Lplus Y a t := by
  unfold Lplus
  exact div_nonneg (le_max_right _ _) (by linarith)

/-- `L⁺` is at most `Y / (4a)` on `[-2a, 2a]`, since there `t² - 4a² ≤ 0`. -/
theorem Lplus_le {Y a t : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) (ht : t ^ 2 ≤ 4 * a ^ 2) :
    Lplus Y a t ≤ Y / (4 * a) := by
  have ha4 : (0 : ℝ) < 4 * a := by linarith
  unfold Lplus
  apply div_le_div_of_nonneg_right ?_ ha4.le
  exact max_le (by linarith) hY

/-- The two halves of `[-a, a]` carry the same integral of `L⁺`, by evenness. -/
theorem integral_Lplus_left_eq_right (Y a : ℝ) :
    (∫ t in (-a)..(0 : ℝ), Lplus Y a t) = ∫ t in (0 : ℝ)..a, Lplus Y a t := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) (f := Lplus Y a)
  rw [neg_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr ?_
  intro t _
  -- `integral_congr` leaves the integrands un-beta-reduced
  change Lplus Y a (-t) = Lplus Y a t
  rw [Lplus_neg]

/-- **Half the area integral.** For `a > 0`, `∫_0^a L⁺(t) dt = 3 · F_Y(a)`.

`integral_Lplus_eq` gives the integral over `[-a, a]`, and `L⁺` is even, so each
half is `3 · F_Y(a)`. -/
theorem integral_Lplus_half {Y a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..a, Lplus Y a t) = 3 * areaF Y a := by
  have hsplit : (∫ t in (-a)..(0 : ℝ), Lplus Y a t) + (∫ t in (0 : ℝ)..a, Lplus Y a t)
      = ∫ t in (-a)..a, Lplus Y a t :=
    intervalIntegral.integral_add_adjacent_intervals
      (Lplus_intervalIntegrable Y a _ _) (Lplus_intervalIntegrable Y a _ _)
  rw [integral_Lplus_left_eq_right, integral_Lplus_eq ha] at hsplit
  linarith

/-- **The step-`6` progression bound on the monotone half.** For a progression
`p, p + 6, …, p + 6(n-1)` inside `[0, a]`, the sum of `L⁺` over it is at most a
sixth of `∫_0^a L⁺` plus one boundary term `Y / (4a)`.

Dropping the largest point and comparing the rest with the integral is what
makes the error a single boundary term: the remaining `n - 1` points have their
whole step-`6` block inside `[0, a]`, so `sum_step_six_le_integral` applies, and
the dropped point contributes at most `L⁺(a) ≤ Y / (4a)`. -/
theorem sum_progression_le {Y a : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) {p : ℝ} (hp : 0 ≤ p)
    {n : ℕ} (hn : ∀ i < n, p + 6 * (i : ℝ) ≤ a) :
    ∑ i ∈ Finset.range n, Lplus Y a (p + 6 * (i : ℝ))
      ≤ (1 / 6) * (∫ t in (0 : ℝ)..a, Lplus Y a t) + Y / (4 * a) := by
  have hnn : ∀ t : ℝ, 0 ≤ Lplus Y a t := fun t => Lplus_nonneg ha t
  have hint0 : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..a, Lplus Y a t :=
    intervalIntegral.integral_nonneg ha.le fun u _ => hnn u
  have hYa : (0 : ℝ) ≤ Y / (4 * a) := by positivity
  rcases n with _ | m
  · simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  · rw [Finset.sum_range_succ]
    have hma : p + 6 * (m : ℝ) ≤ a := hn m (by omega)
    have hm0 : (0 : ℝ) ≤ 6 * (m : ℝ) := by positivity
    -- the dropped point contributes at most one boundary term
    have hlast : Lplus Y a (p + 6 * (m : ℝ)) ≤ Y / (4 * a) := by
      have h1 : Lplus Y a (p + 6 * (m : ℝ)) ≤ Lplus Y a a :=
        Lplus_monotoneOn ha (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr ha.le) hma
      have h2 : Lplus Y a a ≤ Y / (4 * a) := Lplus_le ha hY (by nlinarith)
      linarith
    -- the remaining points sit in blocks inside `[0, a]`
    have hmono : MonotoneOn (Lplus Y a) (Set.Icc p (p + 6 * (m : ℝ))) := by
      intro u hu v hv huv
      exact Lplus_monotoneOn ha (Set.mem_Ici.mpr (le_trans hp hu.1))
        (Set.mem_Ici.mpr (le_trans hp hv.1)) huv
    have hsum := sum_step_six_le_integral (f := Lplus Y a) (p := p) (n := m) hmono
    have hmi : (∫ x in p..(p + 6 * (m : ℝ)), Lplus Y a x)
        ≤ ∫ t in (0 : ℝ)..a, Lplus Y a t :=
      intervalIntegral.integral_mono_interval hp (by linarith) hma
        (Filter.Eventually.of_forall fun t => hnn t) (Lplus_intervalIntegrable Y a _ _)
    linarith

/-- **A residue class in `[0, a]`.** The integers of `[0, a]` congruent to
`s` modulo `6`, for `0 ≤ s`, carry a sum of `L⁺` at most a sixth of `∫_0^a L⁺`
plus `Y / (4a)`.

The class is contained in the step-`6` progression starting at `s`, truncated at
the last term not exceeding `a`; the containment is enough because `L⁺ ≥ 0`. -/
theorem sum_class_Icc_zero_le {Y : ℝ} (hY : 0 ≤ Y) {a : ℤ} (ha : 1 ≤ a) {s : ℤ}
    (hs : 0 ≤ s) :
    ∑ b ∈ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = s}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have hnn : ∀ t : ℝ, 0 ≤ Lplus Y (a : ℝ) t := fun t => Lplus_nonneg ha0 t
  -- the length of the truncated progression
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, (a - s) / 6 < (n : ℤ)
      ∧ ∀ i : ℕ, i < n → s + 6 * (i : ℤ) ≤ a :=
    ⟨((a - s) / 6 + 1).toNat, by omega, fun i hi => by omega⟩
  have hsub : {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = s}
      ⊆ (Finset.range n).image fun i : ℕ => s + 6 * (i : ℤ) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    exact Finset.mem_image.mpr ⟨(b / 6).toNat, Finset.mem_range.mpr (by omega), by omega⟩
  calc ∑ b ∈ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = s}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ ∑ b ∈ (Finset.range n).image fun i : ℕ => s + 6 * (i : ℤ),
          Lplus Y (a : ℝ) (b : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hnn _
    _ = ∑ i ∈ Finset.range n, Lplus Y (a : ℝ) ((s : ℝ) + 6 * (i : ℝ)) := by
        rw [Finset.sum_image fun i _ j _ h => by omega]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        ring
    _ ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) := by
        refine sum_progression_le ha0 hY (by exact_mod_cast hs) fun i hi => ?_
        have := hn2 i hi
        have : ((s + 6 * (i : ℤ) : ℤ) : ℝ) ≤ ((a : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith

/-- **A residue class in `[-a, a]`.** For `0 ≤ r`, the integers of `[-a, a]`
congruent to `r` modulo `6` carry a sum of `L⁺` at most `F_Y(a) + Y / (2a)`.

The interval is split at `0`. On `[0, a]` this is `sum_class_Icc_zero_le`
directly; on `[-a, -1]` the map `b ↦ -b` carries the class into the class of
`-r` modulo `6` inside `[0, a]`, and `L⁺` is even, so the same bound applies.
Two halves at `(1/6) ∫_0^a L⁺ = F_Y(a)/2` each — by `integral_Lplus_half` — give
the main term `F_Y(a)`, and the two boundary terms give `Y / (2a)`. -/
theorem sum_class_le {Y : ℝ} (hY : 0 ≤ Y) {a : ℤ} (ha : 1 ≤ a) {r : ℤ} (hr : 0 ≤ r) :
    ∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = r}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ areaF Y (a : ℝ) + Y / (2 * (a : ℝ)) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have hnn : ∀ t : ℝ, 0 ≤ Lplus Y (a : ℝ) t := fun t => Lplus_nonneg ha0 t
  -- the positive half
  have hpos := sum_class_Icc_zero_le hY ha hr
  -- the negative half, reflected
  have hneg : ∑ b ∈ {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) := by
    have himg : (({b ∈ Finset.Icc (-a) (-1) | b % 6 = r}).image fun b : ℤ => -b)
        ⊆ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = (-r) % 6} := by
      intro c hc
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hc ⊢
      obtain ⟨b, ⟨⟨hb1, hb2⟩, hb3⟩, rfl⟩ := hc
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have heq : ∑ b ∈ {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}, Lplus Y (a : ℝ) (b : ℝ)
        = ∑ c ∈ (({b ∈ Finset.Icc (-a) (-1) | b % 6 = r}).image fun b : ℤ => -b),
            Lplus Y (a : ℝ) (c : ℝ) := by
      rw [Finset.sum_image fun i _ j _ h => by omega]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (((-b : ℤ)) : ℝ) = -((b : ℤ) : ℝ) by push_cast; ring, Lplus_neg]
    rw [heq]
    calc ∑ c ∈ (({b ∈ Finset.Icc (-a) (-1) | b % 6 = r}).image fun b : ℤ => -b),
          Lplus Y (a : ℝ) (c : ℝ)
        ≤ ∑ c ∈ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = (-r) % 6},
            Lplus Y (a : ℝ) (c : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun c _ _ => hnn _
      _ ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) :=
          sum_class_Icc_zero_le hY ha (Int.emod_nonneg _ (by norm_num))
  -- the two halves partition the class
  have hunion : {b ∈ Finset.Icc (-a) a | b % 6 = r}
      = {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}
        ∪ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = r} := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}
      {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = r} := by
    refine Finset.disjoint_left.mpr fun b hb hb' => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb hb'
    omega
  rw [integral_Lplus_half ha0] at hpos hneg
  rw [hunion, Finset.sum_union hdisj]
  have h2a : Y / (4 * (a : ℝ)) + Y / (4 * (a : ℝ)) = Y / (2 * (a : ℝ)) := by
    field_simp
    ring
  linarith

/-- `bClasses` at a multiple of `3` is the `a * c ≡ 2` class set. -/
theorem bClasses_of_three_dvd (a : ℤ) {b : ℤ} (h : 3 ∣ b) :
    bClasses a b = cClasses a 2 := by
  rw [bClasses, ite_eq_left h]

/-- `bClasses` away from the multiples of `3` is the `a * c ≡ 0` class set. -/
theorem bClasses_of_not_three_dvd (a : ℤ) {b : ℤ} (h : ¬ 3 ∣ b) :
    bClasses a b = cClasses a 0 := by
  rw [bClasses, ite_eq_right h]

/-- A set of residue classes modulo `6` has at most `6` members. -/
theorem card_cClasses_le (a : ℤ) (t : ZMod 6) : (cClasses a t).card ≤ 6 := by
  have h : (cClasses a t).card ≤ (Finset.univ : Finset (ZMod 6)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rwa [Finset.card_univ, ZMod.card] at h

/-- The weight is at most `18`, since each of the three class counts it adds is
at most `6`. The exact maximum is `12`, by `weight_values`. -/
theorem weight_le (a : ℤ) : (weight a : ℝ) ≤ 18 := by
  rw [weight_cast]
  have h0 : ((cClasses a 0).card : ℝ) ≤ 6 := by exact_mod_cast card_cClasses_le a 0
  have h2 : ((cClasses a 2).card : ℝ) ≤ 6 := by exact_mod_cast card_cClasses_le a 2
  linarith

/-- **One fibre of the pair count.** For a finite set `P` of pairs `(b, c)` all
completing `a` to a triple of discriminant at most `Y` in the admissible class,
the fibre over a fixed `b` has size at most
`#(bClasses a b) · L⁺(b)/6 + #(bClasses a b)`.

The fibre becomes a set of outer coefficients by `fibre_card_eq_image`, and the
congruence fixes their class modulo `6`: `odd_of_disc` makes `b` odd, and then
`disc_emod_iff_of_three_dvd` and `disc_emod_iff_of_not_three_dvd` give
`a * c ≡ 2` when `3 ∣ b` and `a * c ≡ 0` otherwise — which is exactly the case
split defining `bClasses`. -/
theorem card_fibre_le {Y : ℝ} {a : ℤ} (ha : 1 ≤ a) {P : Finset (ℤ × ℤ)}
    (hP : ∀ p ∈ P, a ≤ p.2 ∧ ((4 * a * p.2 - p.1 ^ 2 : ℤ) : ℝ) ≤ Y ∧
      (4 * a * p.2 - p.1 ^ 2) % 24 = 23) (b : ℤ) :
    ((({p ∈ P | p.1 = b}).card : ℕ) : ℝ)
      ≤ ((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6)
        + ((bClasses a b).card : ℝ) := by
  classical
  rw [fibre_card_eq_image]
  -- the fibre's outer coefficients, with the three constraints transported to `b`
  have hmem : ∀ c ∈ (({p ∈ P | p.1 = b}).image Prod.snd),
      a ≤ c ∧ ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y ∧ (4 * a * c - b ^ 2) % 24 = 23 := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hpP, hpb⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, h3⟩ := hP p hpP
    rw [hpb] at h2 h3
    exact ⟨h1, h2, h3⟩
  have key : ∀ t : ZMod 6, bClasses a b = cClasses a t →
      (∀ c ∈ (({p ∈ P | p.1 = b}).image Prod.snd), ((a * c : ℤ) : ZMod 6) = t) →
      (((({p ∈ P | p.1 = b}).image Prod.snd).card : ℕ) : ℝ)
        ≤ ((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6)
          + ((bClasses a b).card : ℝ) := by
    intro t ht hres
    rw [ht]
    unfold Lplus
    exact card_c_le ha _ (fun c hc => (hmem c hc).1) (fun c hc => (hmem c hc).2.1) hres
  by_cases h3 : (3 : ℤ) ∣ b
  · refine key 2 (bClasses_of_three_dvd a h3) fun c hc => ?_
    obtain ⟨-, -, hdisc⟩ := hmem c hc
    have hodd : Odd b := odd_of_disc hdisc
    rw [mul_assoc] at hdisc
    have h6 : (a * c) % 6 = 2 := (disc_emod_iff_of_three_dvd hodd h3).mp hdisc
    have hcast : ((a * c : ℤ) : ZMod 6) = ((2 : ℤ) : ZMod 6) :=
      (ZMod.intCast_eq_intCast_iff' _ _ _).mpr (by push_cast; omega)
    simpa using hcast
  · refine key 0 (bClasses_of_not_three_dvd a h3) fun c hc => ?_
    obtain ⟨-, -, hdisc⟩ := hmem c hc
    have hodd : Odd b := odd_of_disc hdisc
    rw [mul_assoc] at hdisc
    have h6 : (a * c) % 6 = 0 := (disc_emod_iff_of_not_three_dvd hodd h3).mp hdisc
    have hcast : ((a * c : ℤ) : ZMod 6) = ((0 : ℤ) : ZMod 6) :=
      (ZMod.intCast_eq_intCast_iff' _ _ _).mpr (by push_cast; omega)
    simpa using hcast

/-- **The pair count for a fixed first coefficient, in `Finset` form.** Any
finite set `P` of pairs `(b, c)` completing `a` to a reduced triple of
discriminant at most `Y` in the admissible class satisfies

`#P ≤ w(a)/6 · F_Y(a) + 18 · (Y/a + a)`.

The constant `18` is explicit, no asymptotic notation appearing. It absorbs the
`w(a) ≤ 18` boundary terms of `card_c_le`, one for each of the at most `2a + 1`
values of `b`, and the `w(a)` sum-to-integral errors, each at most `Y/(4a)`, and
nothing further. The main term closes exactly — `card_c_le` carries a `1/6`, each
residue class modulo `6` contributes a sixth of the integral, and
`∫_{-a}^{a} L⁺ = 6 F_Y(a)`. -/
theorem card_pairs_le {Y : ℝ} (hY : 0 ≤ Y) {a : ℤ} (ha : 1 ≤ a) {P : Finset (ℤ × ℤ)}
    (hP : ∀ p ∈ P, |p.1| ≤ a ∧ a ≤ p.2 ∧ ((4 * a * p.2 - p.1 ^ 2 : ℤ) : ℝ) ≤ Y ∧
      (4 * a * p.2 - p.1 ^ 2) % 24 = 23) :
    ((P.card : ℕ) : ℝ)
      ≤ (weight a : ℝ) / 6 * areaF Y (a : ℝ) + 18 * (Y / (a : ℝ) + (a : ℝ)) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  set B : Finset ℤ := {b ∈ Finset.Icc (-a) a | b % 2 = 1} with hBdef
  -- the first coordinate is odd, and reducedness bounds it by `a`
  have hmaps : ∀ p ∈ P, p.1 ∈ B := by
    intro p hp
    obtain ⟨h1, -, -, h4⟩ := hP p hp
    have hodd : p.1 % 2 = 1 := Int.odd_iff.mp (odd_of_disc h4)
    rw [hBdef]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨neg_le_of_abs_le h1, le_of_abs_le h1⟩, hodd⟩
  have hcard : ((P.card : ℕ) : ℝ)
      = ∑ b ∈ B, ((({p ∈ P | p.1 = b}).card : ℕ) : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ => p.1) (t := B)
      fun p hp => hmaps p hp, Nat.cast_sum]
  have hstep : ((P.card : ℕ) : ℝ)
      ≤ ∑ b ∈ B, (((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6)
          + ((bClasses a b).card : ℝ)) := by
    rw [hcard]
    refine Finset.sum_le_sum fun b _ => card_fibre_le ha (fun p hp => ?_) b
    obtain ⟨-, h2, h3, h4⟩ := hP p hp
    exact ⟨h2, h3, h4⟩
  rw [Finset.sum_add_distrib] at hstep
  -- the boundary terms: at most `6` classes for each of at most `2a + 1` values of `b`
  have hbdd : ∀ b : ℤ, ((bClasses a b).card : ℝ) ≤ 6 := by
    intro b
    by_cases h3 : (3 : ℤ) ∣ b
    · rw [bClasses_of_three_dvd a h3]
      exact_mod_cast card_cClasses_le a 2
    · rw [bClasses_of_not_three_dvd a h3]
      exact_mod_cast card_cClasses_le a 0
  have hBcard : ((B.card : ℕ) : ℝ) ≤ 2 * (a : ℝ) + 1 := by
    have h1 : B.card ≤ (Finset.Icc (-a) a).card := by
      rw [hBdef]; exact Finset.card_le_card (Finset.filter_subset _ _)
    rw [Int.card_Icc] at h1
    have h2 : ((B.card : ℕ) : ℤ) ≤ 2 * a + 1 := by omega
    exact_mod_cast h2
  have herr : ∑ b ∈ B, ((bClasses a b).card : ℝ) ≤ 6 * (2 * (a : ℝ) + 1) := by
    calc ∑ b ∈ B, ((bClasses a b).card : ℝ) ≤ ∑ _b ∈ B, (6 : ℝ) :=
          Finset.sum_le_sum fun b _ => hbdd b
      _ = ((B.card : ℕ) : ℝ) * 6 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 6 * (2 * (a : ℝ) + 1) := by linarith
  -- the three odd residue classes modulo `6`
  have hC3 : {b ∈ B | (3 : ℤ) ∣ b} = {b ∈ Finset.Icc (-a) a | b % 6 = 3} := by
    rw [hBdef]
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hC15 : {b ∈ B | ¬ ((3 : ℤ) ∣ b)}
      = {b ∈ Finset.Icc (-a) a | b % 6 = 1} ∪ {b ∈ Finset.Icc (-a) a | b % 6 = 5} := by
    rw [hBdef]
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj15 : Disjoint ({b ∈ Finset.Icc (-a) a | b % 6 = 1} : Finset ℤ)
      {b ∈ Finset.Icc (-a) a | b % 6 = 5} := by
    refine Finset.disjoint_left.mpr fun b hb hb' => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb hb'
    omega
  have e3 : (∑ b ∈ {b ∈ B | (3 : ℤ) ∣ b}, Lplus Y (a : ℝ) (b : ℝ) / 6)
      = (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 3}, Lplus Y (a : ℝ) (b : ℝ)) / 6 := by
    rw [hC3, Finset.sum_div]
  have e15 : (∑ b ∈ {b ∈ B | ¬ ((3 : ℤ) ∣ b)}, Lplus Y (a : ℝ) (b : ℝ) / 6)
      = (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 1}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        + (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 5}, Lplus Y (a : ℝ) (b : ℝ)) / 6 := by
    rw [hC15, Finset.sum_union hdisj15, Finset.sum_div, Finset.sum_div]
  have hb1 := sum_class_le hY ha (r := 1) (by norm_num)
  have hb3 := sum_class_le hY ha (r := 3) (by norm_num)
  have hb5 := sum_class_le hY ha (r := 5) (by norm_num)
  have hc0 : (0 : ℝ) ≤ ((cClasses a 0).card : ℝ) := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ ((cClasses a 2).card : ℝ) := Nat.cast_nonneg _
  -- the main term, with the weight assembled by `sum_bClasses_split`
  have hkey : (∑ b ∈ B, ((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6))
      ≤ (weight a : ℝ) / 6 * areaF Y (a : ℝ)
        + (weight a : ℝ) * (Y / (2 * (a : ℝ))) / 6 := by
    rw [sum_bClasses_split a B fun b => Lplus Y (a : ℝ) (b : ℝ) / 6, e3, e15]
    have t1 : (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 3}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        ≤ (areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6 := by linarith
    have t2 : (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 1}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        + (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 5}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        ≤ 2 * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6) := by linarith
    have p1 := mul_le_mul_of_nonneg_left t1 hc2
    have p2 := mul_le_mul_of_nonneg_left t2 hc0
    calc ((cClasses a 2).card : ℝ)
            * ((∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 3}, Lplus Y (a : ℝ) (b : ℝ)) / 6)
          + ((cClasses a 0).card : ℝ)
            * ((∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 1}, Lplus Y (a : ℝ) (b : ℝ)) / 6
              + (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 5}, Lplus Y (a : ℝ) (b : ℝ)) / 6)
        ≤ ((cClasses a 2).card : ℝ) * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6)
          + ((cClasses a 0).card : ℝ)
            * (2 * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6)) := by linarith
      _ = (2 * ((cClasses a 0).card : ℝ) + ((cClasses a 2).card : ℝ))
            * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6) := by ring
      _ = (weight a : ℝ) * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6) := by
          rw [← weight_cast a]
      _ = (weight a : ℝ) / 6 * areaF Y (a : ℝ)
            + (weight a : ℝ) * (Y / (2 * (a : ℝ))) / 6 := by ring
  -- collect the two error contributions into `18 · (Y/a + a)`
  have hE : (0 : ℝ) ≤ Y / (2 * (a : ℝ)) := by positivity
  have hYd : Y / (2 * (a : ℝ)) = Y / (a : ℝ) / 2 := by rw [div_div, mul_comm]
  have hYa0 : (0 : ℝ) ≤ Y / (a : ℝ) := by positivity
  have hprod : (weight a : ℝ) * (Y / (2 * (a : ℝ))) / 6
      ≤ 18 * (Y / (2 * (a : ℝ))) / 6 := by
    have h := mul_le_mul_of_nonneg_right (weight_le a) hE
    linarith
  linarith

/-- The pairs `(b, c)` completing a fixed `a ≥ 1` to a reduced triple of
discriminant at most `Y` form a finite set: reducedness bounds `b` by `a`, and
the discriminant bound caps `c`. -/
theorem pairs_finite (Y : ℝ) {a : ℤ} (ha : 1 ≤ a) :
    {p : ℤ × ℤ | (a, p.1, p.2) ∈ reducedTriplesUpTo Y}.Finite := by
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have hfin : (Set.Icc (-a) a ×ˢ Set.Icc a ⌈(Y + (a : ℝ) ^ 2) / (4 * (a : ℝ))⌉).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine hfin.subset ?_
  rintro ⟨b, c⟩ hp
  obtain ⟨h1, h2, -, h4, -⟩ : |b| ≤ a ∧ a ≤ c ∧ 0 < 4 * a * c - b ^ 2 ∧
      ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y ∧ (4 * a * c - b ^ 2) % 24 = 23 := hp
  have hb2 : ((b : ℝ)) ^ 2 ≤ ((a : ℝ)) ^ 2 := by
    have hz : b ^ 2 ≤ a ^ 2 := by
      calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
        _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
    exact_mod_cast hz
  have hc : (c : ℝ) ≤ (Y + (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (a : ℝ))]
    push_cast at h4
    linarith
  refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨neg_le_of_abs_le h1, le_of_abs_le h1⟩,
    Set.mem_Icc.mpr ⟨h2, ?_⟩⟩
  exact Int.cast_le.mp (hc.trans (Int.le_ceil _))

/-- **`lem_triple_count_a`.** There is an explicit constant `C > 0` — namely
`C = 18` — such that for every `Y ≥ 1` and every integer `a` with `1 ≤ a` and
`3a² ≤ Y`,

`#{(b, c) : (a, b, c) ∈ T*(Y)} ≤ w(a)/6 · F_Y(a) + C · (Y/a + a)`.

The range is recorded as `3a² ≤ Y` rather than as `1 ≤ a ≤ √(Y/3)`; the two are
equivalent for `a ≥ 0`. The upper bound on `a` is not needed for the inequality:
`card_pairs_le` establishes it for every `a ≥ 1`, the positive part in `L⁺`
making the count vacuously bounded once `4a² > Y + b²`. -/
@[pz_tag "lem_triple_count_a"]
theorem exists_const_card_pairs_le :
    ∃ C > 0, ∀ Y : ℝ, 1 ≤ Y → ∀ a : ℤ, 1 ≤ a → 3 * (a : ℝ) ^ 2 ≤ Y →
      (({p : ℤ × ℤ | (a, p.1, p.2) ∈ reducedTriplesUpTo Y}.ncard : ℕ) : ℝ)
        ≤ (weight a : ℝ) / 6 * areaF Y (a : ℝ) + C * (Y / (a : ℝ) + (a : ℝ)) := by
  refine ⟨18, by norm_num, fun Y hY a ha _ => ?_⟩
  classical
  have hfin := pairs_finite Y ha
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine card_pairs_le (by linarith) ha fun p hp => ?_
  rw [Set.Finite.mem_toFinset] at hp
  obtain ⟨h1, h2, -, h4, h5⟩ := hp
  exact ⟨h1, h2, h4, h5⟩

end PartitionZheng
