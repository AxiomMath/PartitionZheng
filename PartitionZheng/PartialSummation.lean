/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.FIntegral
public import PartitionZheng.Weight

/-!
# The weighted sum against the area function

The lattice count produces the weighted sum `∑_{1 ≤ a ≤ √(Y/3)} (w a / 6) F_Y(a)`,
and the class-number average needs it bounded by `(π/108) Y^{3/2} + C Y log Y`.

The mean of `w / 6` over a period of six is `1`, so the weighted sum ought to be
comparable with the unweighted one. Here the comparison is an inequality with no
error term at all, for a reason particular to how the six values sit in the
period: they are `1/2, 1, 1, 1, 1/2, 2` at `a ≡ 1, 2, 3, 4, 5, 0 [MOD 6]`, so on
a block `{6m+1, …, 6m+6}` the one coefficient exceeding `1` sits at the *last*
index, where the nonincreasing `F_Y` is smallest, and the two deficits of `1/2`
sit earlier, where it is larger. From `F_Y(6m+6) ≤ F_Y(6m+1)` and
`F_Y(6m+6) ≤ F_Y(6m+5)` one gets
`F_Y(6m+6) ≤ F_Y(6m+1)/2 + F_Y(6m+5)/2`, which says exactly that the weighted
block does not exceed the unweighted block. The residues `1, …, 5` of an
incomplete final block carry coefficients at most `1` and so need no
compensation. Hence the weight may be dropped outright, and since `F_Y` is
nonincreasing the remaining sum is at most `∫_0^∞ F_Y(a) da`.

`Y ^ (3/2)` is written `Y * sqrt Y`, as elsewhere in this development.

## Main results

* `PartitionZheng.areaF_antitoneOn` — `F_Y` is nonincreasing on `(0, ∞)`.
* `PartitionZheng.sum_areaF_le_integral` — `∑_{1 ≤ a ≤ N} F_Y(a) ≤ ∫_0^∞ F_Y(a) da`.
* `PartitionZheng.weighted_areaF_sum_le` — the weighted sum is at most
  `(π/108) Y^{3/2}`.
* `PartitionZheng.exists_weighted_areaF_sum_le` — the bound in the form the
  source states it, with an error term `C Y log Y`.
-/

@[expose] public section

namespace PartitionZheng

open MeasureTheory

/-! ### The area function is nonnegative and nonincreasing -/

/-- `F_Y` is nonnegative for `a > 0`, being a positive multiple of the integral of
a positive part. -/
theorem areaF_nonneg (Y : ℝ) {a : ℝ} (ha : 0 < a) : 0 ≤ areaF Y a := by
  have h : (0 : ℝ) ≤ ∫ t in (-a)..a, max (Y + t ^ 2 - 4 * a ^ 2) 0 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => le_max_right _ _
  unfold areaF
  exact mul_nonneg (div_nonneg zero_le_one (by linarith)) h

/-- `F_Y` is nonincreasing on `(0, ∞)`. In the shape `areaF_subst` gives, the
integrand `(Y - a²(4 - σ²))₊` is nonincreasing in `a` pointwise, because
`4 - σ² ≥ 3 > 0` throughout the range of integration. -/
theorem areaF_antitoneOn (Y : ℝ) : AntitoneOn (areaF Y) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hcont : ∀ c : ℝ, IntervalIntegrable
      (fun σ : ℝ => max (Y + c ^ 2 * σ ^ 2 - 4 * c ^ 2) 0) volume (-1) 1 := fun c =>
    (((continuous_const.add (continuous_const.mul (continuous_pow 2))).sub
      continuous_const).max continuous_const).intervalIntegrable _ _
  have key : (∫ σ in (-1 : ℝ)..1, max (Y + b ^ 2 * σ ^ 2 - 4 * b ^ 2) 0)
      ≤ ∫ σ in (-1 : ℝ)..1, max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0 := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hcont b) (hcont a) fun σ hσ => ?_
    obtain ⟨hσ1, hσ2⟩ := hσ
    have hsq : σ ^ 2 ≤ 1 := by nlinarith
    have hab2 : a ^ 2 ≤ b ^ 2 := by nlinarith
    have hmul : a ^ 2 * (4 - σ ^ 2) ≤ b ^ 2 * (4 - σ ^ 2) :=
      mul_le_mul_of_nonneg_right hab2 (by linarith)
    exact max_le_max (by linarith) le_rfl
  rw [areaF_subst ha, areaF_subst hb]
  linarith

/-! ### The weight as a real coefficient -/

/-- `weight` reads its argument modulo `6`, so on a natural number it is
determined by the remainder. -/
private theorem weight_natCast_mod (a : ℕ) : weight (a : ℤ) = weight ((a % 6 : ℕ) : ℤ) :=
  weight_eq_of_cast (by simp only [Int.cast_natCast, ZMod.natCast_mod])

/-- The coefficient `w a / 6` depends only on the remainder of `a` modulo `6`. -/
private theorem weight_div_six_of_mod {a r : ℕ} (h : a % 6 = r) :
    (weight (a : ℤ) : ℝ) / 6 = (weight (r : ℤ) : ℝ) / 6 := by
  rw [weight_natCast_mod, h]

/-- Away from `a ≡ 0 [MOD 6]` the coefficient `w a / 6` is at most `1`: the five
remaining values of `w` are `3, 6, 6, 6, 3`. -/
private theorem weight_div_six_le_one {a : ℕ} (h : a % 6 ≠ 0) :
    (weight (a : ℤ) : ℝ) / 6 ≤ 1 := by
  obtain ⟨-, w1, w2, w3, w4, w5⟩ := weight_values
  have h6 : a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by omega
  rw [weight_natCast_mod]
  rcases h6 with h' | h' | h' | h' | h' <;> rw [h'] <;> norm_num [w1, w2, w3, w4, w5]

/-! ### Dropping the weight

The coefficient `w a / 6` can be replaced by `1` throughout, at no cost, for any
nonnegative nonincreasing `f` in place of `F_Y`. -/

section Dropping

variable {f : ℕ → ℝ}

/-- A sum over `Ioc p (p + n)` reindexed as a sum over `range n`. -/
private theorem sum_Ioc_eq_sum_range (g : ℕ → ℝ) (p n : ℕ) :
    ∑ a ∈ Finset.Ioc p (p + n), g a = ∑ j ∈ Finset.range n, g (p + (j + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : p + (k + 1) = p + k + 1 := rfl
      rw [hstep, Finset.sum_Ioc_succ_top (Nat.le_add_right p k), ih, Finset.sum_range_succ]
      rfl

/-- **One complete block of six.** The coefficients on `{6m+1, …, 6m+6}` are
`1/2, 1, 1, 1, 1/2, 2`, and the only one exceeding `1` sits at the last index,
where a nonincreasing `f` is smallest. Since `f (6m+6) ≤ f (6m+1)` and
`f (6m+6) ≤ f (6m+5)`, the excess `f (6m+6)` is covered by the two deficits
`f (6m+1)/2` and `f (6m+5)/2`. -/
private theorem weighted_block_le (hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → f j ≤ f i) (m : ℕ) :
    ∑ a ∈ Finset.Ioc (6 * m) (6 * m + 6), (weight (a : ℤ) : ℝ) / 6 * f a
      ≤ ∑ a ∈ Finset.Ioc (6 * m) (6 * m + 6), f a := by
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := weight_values
  have c1 : (weight ((6 * m + 1 : ℕ) : ℤ) : ℝ) / 6 = 1 / 2 := by
    rw [weight_div_six_of_mod (show (6 * m + 1) % 6 = 1 from by omega)]; norm_num [w1]
  have c2 : (weight ((6 * m + 2 : ℕ) : ℤ) : ℝ) / 6 = 1 := by
    rw [weight_div_six_of_mod (show (6 * m + 2) % 6 = 2 from by omega)]; norm_num [w2]
  have c3 : (weight ((6 * m + 3 : ℕ) : ℤ) : ℝ) / 6 = 1 := by
    rw [weight_div_six_of_mod (show (6 * m + 3) % 6 = 3 from by omega)]; norm_num [w3]
  have c4 : (weight ((6 * m + 4 : ℕ) : ℤ) : ℝ) / 6 = 1 := by
    rw [weight_div_six_of_mod (show (6 * m + 4) % 6 = 4 from by omega)]; norm_num [w4]
  have c5 : (weight ((6 * m + 5 : ℕ) : ℤ) : ℝ) / 6 = 1 / 2 := by
    rw [weight_div_six_of_mod (show (6 * m + 5) % 6 = 5 from by omega)]; norm_num [w5]
  have c6 : (weight ((6 * m + 6 : ℕ) : ℤ) : ℝ) / 6 = 2 := by
    rw [weight_div_six_of_mod (show (6 * m + 6) % 6 = 0 from by omega)]; norm_num [w0]
  have h1 : f (6 * m + 6) ≤ f (6 * m + 1) := hanti _ _ (by omega) (by omega)
  have h5 : f (6 * m + 6) ≤ f (6 * m + 5) := hanti _ _ (by omega) (by omega)
  rw [sum_Ioc_eq_sum_range, sum_Ioc_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only
  rw [c1, c2, c3, c4, c5, c6]
  linarith

/-- The weight can be dropped over a range consisting of complete blocks of
six. -/
private theorem weighted_sum_blocks_le (hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → f j ≤ f i) (q : ℕ) :
    ∑ a ∈ Finset.Ioc 0 (6 * q), (weight (a : ℤ) : ℝ) / 6 * f a
      ≤ ∑ a ∈ Finset.Ioc 0 (6 * q), f a := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq : 6 * (q + 1) = 6 * q + 6 := by ring
      rw [hq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) 6),
        ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) 6)]
      exact add_le_add ih (weighted_block_le hanti q)

/-- **The weight drops out.** For nonnegative nonincreasing `f`, the weighted sum
over `1 ≤ a ≤ N` is at most the unweighted one: the complete blocks of six are
handled by `weighted_block_le`, and the at most five remaining indices are
congruent to `1, …, 5` modulo `6`, where the coefficient is already at most
`1`. -/
private theorem weighted_sum_le_sum (hnn : ∀ a : ℕ, 1 ≤ a → 0 ≤ f a)
    (hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → f j ≤ f i) (N : ℕ) :
    ∑ a ∈ Finset.Ioc 0 N, (weight (a : ℤ) : ℝ) / 6 * f a ≤ ∑ a ∈ Finset.Ioc 0 N, f a := by
  obtain ⟨q, r, hr, hN⟩ : ∃ q r, r < 6 ∧ N = 6 * q + r := ⟨N / 6, N % 6, by omega, by omega⟩
  subst hN
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) r),
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) r)]
  refine add_le_add (weighted_sum_blocks_le hanti q) (Finset.sum_le_sum fun a ha => ?_)
  simp only [Finset.mem_Ioc] at ha
  calc (weight (a : ℤ) : ℝ) / 6 * f a
      ≤ 1 * f a :=
        mul_le_mul_of_nonneg_right (weight_div_six_le_one (by omega)) (hnn a (by omega))
    _ = f a := one_mul _

end Dropping

/-! ### From the sum to the integral -/

/-- `lem_F_integral` forces `F_Y` to be integrable on `(0, ∞)`: were it not, the
integral would be `0` by convention, whereas the value the lemma assigns it is
positive. -/
theorem integrableOn_areaF {Y : ℝ} (hY : 0 < Y)
    (hFY : (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = Real.pi / 108 * (Y * Real.sqrt Y)) :
    IntegrableOn (areaF Y) (Set.Ioi 0) := by
  by_contra hcon
  rw [MeasureTheory.integral_undef hcon] at hFY
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hpos : 0 < Real.pi / 108 * (Y * Real.sqrt Y) :=
    mul_pos (by positivity) (mul_pos hY hs)
  linarith

/-- **The sum is below the integral.** Each term `F_Y(k+1)` is at most the
integral of `F_Y` over `(k, k+1]`, since `F_Y` is nonincreasing there and the
interval has length `1`; the unit intervals for `1 ≤ k + 1 ≤ N` tile `(0, N]`,
and the remaining part of `(0, ∞)` contributes nonnegatively. -/
theorem sum_areaF_le_integral {Y : ℝ} (hint : IntegrableOn (areaF Y) (Set.Ioi 0)) (N : ℕ) :
    ∑ a ∈ Finset.Ioc 0 N, areaF Y (a : ℝ) ≤ ∫ a in Set.Ioi (0 : ℝ), areaF Y a := by
  have hsub : ∀ k : ℕ, Set.Ioc (k : ℝ) ((k : ℝ) + 1) ⊆ Set.Ioi (0 : ℝ) := fun k x hx =>
    lt_of_le_of_lt (Nat.cast_nonneg k) hx.1
  have hii : ∀ k : ℕ, IntervalIntegrable (areaF Y) volume (k : ℝ) ((k : ℝ) + 1) := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hint.mono_set (hsub k)
  have hterm : ∀ k : ℕ, areaF Y ((k : ℝ) + 1) ≤ ∫ x in (k : ℝ)..((k : ℝ) + 1), areaF Y x := by
    intro k
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle : ∀ x ∈ Set.Ioc (k : ℝ) ((k : ℝ) + 1), areaF Y ((k : ℝ) + 1) ≤ areaF Y x :=
      fun x hx => areaF_antitoneOn Y (hsub k hx) (Set.mem_Ioi.mpr hpos) hx.2
    have hfin : volume (Set.Ioc (k : ℝ) ((k : ℝ) + 1)) ≠ ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have h := setIntegral_ge_of_const_le_real measurableSet_Ioc hfin hle
      (hint.mono_set (hsub k))
    have hvol : (volume : Measure ℝ).real (Set.Ioc (k : ℝ) ((k : ℝ) + 1)) = 1 := by
      simp [Measure.real, Real.volume_Ioc]
    rw [hvol, mul_one] at h
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact h
  have htel : ∑ k ∈ Finset.range N, (∫ x in (k : ℝ)..((k : ℝ) + 1), areaF Y x)
      = ∫ x in (0 : ℝ)..(N : ℝ), areaF Y x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := areaF Y) (μ := volume)
      (a := fun k : ℕ => (k : ℝ)) (n := N) fun k _ => by simpa using hii k
    simpa using h
  have hmono : (∫ x in Set.Ioc (0 : ℝ) (N : ℝ), areaF Y x)
      ≤ ∫ x in Set.Ioi (0 : ℝ), areaF Y x := by
    refine setIntegral_mono_set hint ?_ Set.Ioc_subset_Ioi_self.eventuallyLE
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => areaF_nonneg Y hx)
  calc ∑ a ∈ Finset.Ioc 0 N, areaF Y (a : ℝ)
      = ∑ k ∈ Finset.range N, areaF Y ((k : ℝ) + 1) := by
        simpa using sum_Ioc_eq_sum_range (fun a => areaF Y (a : ℝ)) 0 N
    _ ≤ ∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), areaF Y x :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ∫ x in (0 : ℝ)..(N : ℝ), areaF Y x := htel
    _ = ∫ x in Set.Ioc (0 : ℝ) (N : ℝ), areaF Y x :=
        intervalIntegral.integral_of_le (Nat.cast_nonneg N)
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), areaF Y x := hmono

/-! ### The weighted sum -/

/-- **The weighted sum, with no error term.** For every `N`,
`∑_{1 ≤ a ≤ N} (w a / 6) F_Y(a) ≤ (π/108) Y^{3/2}`.

The hypothesis `hFY` is `lem_F_integral` at `Y`. -/
theorem weighted_areaF_sum_le {Y : ℝ} (hY : 0 < Y)
    (hFY : (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = Real.pi / 108 * (Y * Real.sqrt Y)) (N : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
      ≤ Real.pi / 108 * (Y * Real.sqrt Y) := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hnn : ∀ a : ℕ, 1 ≤ a → 0 ≤ areaF Y (a : ℝ) := fun a ha =>
    areaF_nonneg Y (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha)
  have hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → areaF Y (j : ℝ) ≤ areaF Y (i : ℝ) := by
    intro i j hi hij
    have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hi
    have hj' : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le hi' (by exact_mod_cast hij)
    exact areaF_antitoneOn Y (Set.mem_Ioi.mpr hi') (Set.mem_Ioi.mpr hj') (by exact_mod_cast hij)
  rw [hIcc]
  calc ∑ a ∈ Finset.Ioc 0 N, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
      ≤ ∑ a ∈ Finset.Ioc 0 N, areaF Y (a : ℝ) := weighted_sum_le_sum hnn hanti N
    _ ≤ ∫ a in Set.Ioi (0 : ℝ), areaF Y a := sum_areaF_le_integral (integrableOn_areaF hY hFY) N
    _ = Real.pi / 108 * (Y * Real.sqrt Y) := hFY

/-- **`lem_partial_summation`.** There is a constant `C > 0` such that for every
real `Y ≥ 2`,

`∑_{1 ≤ a ≤ √(Y/3)} (w a / 6) F_Y(a) ≤ (π/108) Y^{3/2} + C Y log Y`.

The hypothesis `hF` is `lem_F_integral`, `∫_0^∞ F_Y(a) da = (π/108) Y^{3/2}` for
every `Y > 0`; it will be discharged once that lemma is available.

`weighted_areaF_sum_le` gives the bound without the error term, so any positive
`C` will do here. -/
@[pz_tag "lem_partial_summation"]
theorem exists_weighted_areaF_sum_le
    (hF : ∀ Y : ℝ, 0 < Y →
      (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = Real.pi / 108 * (Y * Real.sqrt Y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
        ≤ Real.pi / 108 * (Y * Real.sqrt Y) + C * (Y * Real.log Y) := by
  refine ⟨1, one_pos, fun Y hY2 => ?_⟩
  have hY : 0 < Y := by linarith
  have hlog : 0 < Y * Real.log Y := mul_pos hY (Real.log_pos (by linarith))
  have h := weighted_areaF_sum_le hY (hF Y hY) ⌊Real.sqrt (Y / 3)⌋₊
  linarith

end PartitionZheng
