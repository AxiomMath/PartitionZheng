/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import PartitionZheng.Meta.Attr

/-!
# The Möbius series at two

The unrestricted series is

`∑_n μ(n) / n² = 1 / ζ(2) = 6 / π²`,

which comes from Mathlib: `LSeries_one_mul_Lseries_moebius` gives
`ζ(s) · L(μ,s) = 1` for `1 < re s`, and `riemannZeta_two` evaluates `ζ(2)`.

Restricting to the `n` coprime to `6` needs no Euler-product machinery: every
square-free `n` factors uniquely as `n = e * m` with `e` supported on `{2, 3}`
and `gcd (m, 6) = 1`, and `μ` is multiplicative on coprimes, so

`∑ₙ μ(n)/n² = (∑_{e ∣ 6} μ(e)/e²) * (∑_{(m,6)=1} μ(m)/m²)`.

The first factor is `(1 - 2⁻²)(1 - 3⁻²) = 2/3`, so the restricted sum is
`(6/π²) / (2/3) = 9/π²`. That value is the Euler product
`∏_{p ≥ 5} (1 - p⁻²) = 9 / π²` written as a series.

## Main definitions

* `PartitionZheng.coprimeSummand` — `μ(m)/m²` on the `m` coprime to `6`.

## Main results

* `PartitionZheng.moebius_lseries_two` — `L(μ, 2) = 6 / π²`.
* `PartitionZheng.summable_moebius_div_sq` — real summability.
* `PartitionZheng.moebius_tsum_real` — `∑ₙ μ(n)/n² = 6/π²` over `ℝ`.
* `PartitionZheng.coprime_moebius_tsum` — `∑_{(m,6)=1} μ(m)/m² = 9/π²`.
-/

@[expose] public section

namespace PartitionZheng

open Real Complex

/-- `1 < re 2`, the summability side condition of the Dirichlet identities. -/
private lemma one_lt_re_two : (1 : ℝ) < ((2 : ℂ)).re := by
  norm_num

/-- The Möbius `L`-series at `2` is `6 / π²`, i.e. `1 / ζ(2)`. -/
theorem moebius_lseries_two :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 = 6 / (Real.pi : ℂ) ^ 2 := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := LSeries_one_mul_Lseries_moebius one_lt_re_two
  rw [LSeries_one_eq_riemannZeta one_lt_re_two, riemannZeta_two] at h
  -- `h : (π : ℂ) ^ 2 / 6 * L(μ, 2) = 1`
  field_simp at h
  field_simp
  linear_combination h

/-- The Euler factor at `2` and `3`: `∑_{e ∣ 6} μ(e) / e² = 2/3`.

Equivalently `(1 - 2⁻²)(1 - 3⁻²) = (3/4)(8/9) = 2/3`. It is the constant relating
the unrestricted series to its restriction to the `n` coprime to `6`:
`(2/3) · (9/π²) = 6/π²`. -/
theorem moebius_factor_six :
    ∑ e ∈ Nat.divisors 6, (ArithmeticFunction.moebius e : ℚ) / (e : ℚ) ^ 2 = 2 / 3 := by
  have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  have hmu6 : ArithmeticFunction.moebius 6 = 1 := by
    have h23 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h23, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [h6]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three, hmu6]
  norm_num

/-- Consistency of the two constants: `(2/3) * (9/π²) = 6/π²`. -/
theorem factor_six_consistent :
    (2 / 3 : ℝ) * (9 / Real.pi ^ 2) = 6 / Real.pi ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `μ (p ^ e) = 0` for `e ≥ 2`: `p ^ e` is not square-free. -/
theorem moebius_prime_pow_eq_zero {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    ArithmeticFunction.moebius (p ^ e) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsf
  have hdvd : p * p ∣ p ^ e := by
    have : p ^ 2 ∣ p ^ e := pow_dvd_pow p he
    simpa [pow_two] using this
  have := hsf p hdvd
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)

/-- The local Euler factor of the Möbius series at a prime `p`:
`∑_e μ(p^e) / (p^e)² = 1 - p⁻²`. Only `e = 0` and `e = 1` contribute, since
`p^e` is not square-free beyond that. -/
theorem local_factor {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2
      = 1 - ((p : ℝ) ^ 2)⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  -- the summand vanishes for `e ≥ 2`, so the series is a two-term sum
  have hzero : ∀ e, 2 ≤ e →
      (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2 = 0 := by
    intro e he
    rw [moebius_prime_pow_eq_zero hp he]
    simp
  have hHS : HasSum (fun e : ℕ => (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2)
      (∑ e ∈ ({0, 1} : Finset ℕ),
        (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    exact hzero b (by omega)
  rw [hHS.tsum_eq, Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [pow_zero, pow_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp]
  have hpne : ((p : ℝ)) ≠ 0 := ne_of_gt hp0
  field_simp
  push_cast
  ring

/-- `|μ n| ≤ 1`: the Möbius function takes values in `{-1, 0, 1}`. -/
theorem abs_moebius_le_one (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  rcases eq_or_ne (ArithmeticFunction.moebius n) 0 with h | h
  · rw [h]; norm_num
  · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h with h1 | h1 <;>
      rw [h1] <;> norm_num

/-- The Möbius series at `2` is summable over the reals, by comparison with
`∑ 1/n²`. -/
theorem summable_moebius_div_sq :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  refine hp.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [abs_of_pos hsq, one_div]
    rw [div_le_iff₀ hsq]
    have := abs_moebius_le_one n
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := this
      _ = ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 2 := by
          field_simp

/-- **The Möbius series at two, over the reals.** `∑ₙ μ(n)/n² = 6/π²`.

The real series and the `L`-series agree termwise with no special case at
`n = 0`: `LSeries.term` is `0` there by definition, and on the real side
`μ 0 = 0` makes the term `0 / 0`, which Lean evaluates to `0`. -/
theorem moebius_tsum_real :
    ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
      = 6 / Real.pi ^ 2 := by
  have hsum := summable_moebius_div_sq
  -- push the real `HasSum` into `ℂ`
  have hC : HasSum (fun n : ℕ =>
      ((((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ))
      (((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ) :=
    hsum.hasSum.map (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom
      Complex.continuous_ofReal
  -- termwise it is the `L`-series summand at `s = 2`
  have hterm : ∀ n : ℕ,
      ((((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ)
        = LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) 2 n := by
    intro n
    rw [LSeries.term_def]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · rw [ite_eq_right (by omega : ¬ (n = 0))]
      -- the `L`-series exponent is a `cpow`; convert it to a monoid power
      have hcast : ((n : ℂ)) ^ (2 : ℂ) = ((n : ℂ)) ^ (2 : ℕ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      rw [hcast]
      push_cast
      ring
  have hC' : HasSum (LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) 2)
      (((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ) := by
    simpa only [hterm] using hC
  -- so the real sum casts to `L(μ, 2) = 6/π²`
  have hval := hC'.tsum_eq
  rw [← LSeries, moebius_lseries_two] at hval
  have hre : (((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ)
      = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    rw [← hval]; push_cast; ring
  exact_mod_cast hre

/-- The Euler factor at `2` and `3`, over the reals: `∑_{e ∣ 6} μ(e)/e² = 2/3`.
The `ℚ` version is `moebius_factor_six`. -/
theorem moebius_factor_six_real :
    ∑ e ∈ Nat.divisors 6, (ArithmeticFunction.moebius e : ℝ) / (e : ℝ) ^ 2 = 2 / 3 := by
  have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  have hmu6 : ArithmeticFunction.moebius 6 = 1 := by
    have h23 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h23, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [h6]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three, hmu6]
  norm_num

/-! ### The coprime decomposition `n = e * m`, `e ∣ 6`, `gcd (m, 6) = 1`

The arithmetic behind the factorization
`∑ₙ μ(n)/n² = (∑_{e ∣ 6} μ(e)/e²) * (∑_{(m,6)=1} μ(m)/m²)`: the decomposition
exists on the support of `μ`, it is unique, and the two factors are coprime so
`μ` splits across it. -/

/-- A divisor of `6` is coprime to anything coprime to `6`. -/
theorem coprime_of_dvd_six {e m : ℕ} (he : e ∣ 6) (hm : Nat.Coprime m 6) :
    Nat.Coprime e m := by
  have h1 : Nat.gcd e m ∣ 6 := dvd_trans (Nat.gcd_dvd_left e m) he
  have h2 : Nat.gcd e m ∣ m := Nat.gcd_dvd_right e m
  have h3 : Nat.gcd e m ∣ Nat.gcd m 6 := Nat.dvd_gcd h2 h1
  rw [hm] at h3
  exact Nat.dvd_one.mp h3

/-- The decomposition is unique: the `{2,3}`-part and the coprime part are each
determined. -/
theorem six_part_unique {e₁ e₂ m₁ m₂ : ℕ} (he₁ : e₁ ∣ 6) (he₂ : e₂ ∣ 6)
    (hm₁ : Nat.Coprime m₁ 6) (hm₂ : Nat.Coprime m₂ 6)
    (hp₁ : 0 < e₁) (h : e₁ * m₁ = e₂ * m₂) : e₁ = e₂ ∧ m₁ = m₂ := by
  have hc12 : Nat.Coprime e₁ m₂ := coprime_of_dvd_six he₁ hm₂
  have hc21 : Nat.Coprime e₂ m₁ := coprime_of_dvd_six he₂ hm₁
  have hd1 : e₁ ∣ e₂ := by
    have hdd : e₁ ∣ e₂ * m₂ := h ▸ (Dvd.intro m₁ rfl)
    exact hc12.dvd_of_dvd_mul_right hdd
  have hd2 : e₂ ∣ e₁ := by
    have hdd : e₂ ∣ e₁ * m₁ := h ▸ (Dvd.intro m₂ rfl)
    exact hc21.dvd_of_dvd_mul_right hdd
  have hee : e₁ = e₂ := Nat.dvd_antisymm hd1 hd2
  refine ⟨hee, ?_⟩
  rw [hee] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

/-- **The decomposition exists** on the support of `μ`: a square-free `n`
factors as `e * m` with `e ∣ 6` and `gcd (m, 6) = 1`, namely `e = gcd (n, 6)`.

Square-freeness is what makes this work — for `n = 4` the `{2,3}`-part is `4`,
not a divisor of `6`. That is harmless because `μ` vanishes there. -/
theorem exists_six_decomp {n : ℕ} (hsf : Squarefree n) :
    ∃ e m : ℕ, e ∣ 6 ∧ Nat.Coprime m 6 ∧ n = e * m := by
  set g : ℕ := Nat.gcd n 6 with hg
  have hgn : g ∣ n := Nat.gcd_dvd_left n 6
  have hg6 : g ∣ 6 := Nat.gcd_dvd_right n 6
  refine ⟨g, n / g, hg6, ?_, ?_⟩
  · -- `n / g` is coprime to `6`: a common prime `p` would give `p² ∣ n`
    by_contra hc
    obtain ⟨p, hp, hpk, hp6⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpn : p ∣ n := dvd_trans hpk (Nat.div_dvd_of_dvd hgn)
    have hpg : p ∣ g := Nat.dvd_gcd hpn hp6
    have hsq : p * p ∣ n := by
      have hmul : n / g * g = n := Nat.div_mul_cancel hgn
      calc p * p ∣ (n / g) * g := mul_dvd_mul hpk hpg
        _ = n := hmul
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p hsq))
  · exact (Nat.div_mul_cancel hgn).symm ▸ (Nat.mul_div_cancel' hgn).symm

/-! ### Reindexing the Möbius series along the decomposition -/

/-- The index type of the coprime decomposition: a divisor of `6` paired with a
natural coprime to `6`. -/
abbrev SixIdx : Type := ↥(Nat.divisors 6) × {m : ℕ // Nat.Coprime m 6}

/-- The decomposition map `(e, m) ↦ e * m`. -/
def sixMul (p : SixIdx) : ℕ := p.1.val * p.2.val

/-- `sixMul` is injective, by `six_part_unique`. -/
theorem sixMul_injective : Function.Injective sixMul := by
  rintro ⟨⟨e₁, he₁⟩, ⟨m₁, hm₁⟩⟩ ⟨⟨e₂, he₂⟩, ⟨m₂, hm₂⟩⟩ h
  simp only [sixMul] at h
  have hd₁ : e₁ ∣ 6 := (Nat.mem_divisors.mp he₁).1
  have hd₂ : e₂ ∣ 6 := (Nat.mem_divisors.mp he₂).1
  have hp₁ : 0 < e₁ := Nat.pos_of_mem_divisors he₁
  obtain ⟨hee, hmm⟩ := six_part_unique hd₁ hd₂ hm₁ hm₂ hp₁ h
  subst hee
  subst hmm
  rfl

/-- Off the range of `sixMul` the Möbius summand vanishes: such an `n` is not
square-free, since `exists_six_decomp` decomposes every square-free number. -/
theorem moebius_div_sq_eq_zero_of_notMem_range {n : ℕ} (h : n ∉ Set.range sixMul) :
    (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 = 0 := by
  by_cases hmu : ArithmeticFunction.moebius n = 0
  · rw [hmu]; simp
  · -- `μ n ≠ 0` makes `n` square-free, so it decomposes and lies in the range
    exfalso
    have hsf : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    obtain ⟨e, m, he, hm, hnem⟩ := exists_six_decomp hsf
    refine h ⟨⟨⟨e, Nat.mem_divisors.mpr ⟨he, by norm_num⟩⟩, ⟨m, hm⟩⟩, ?_⟩
    simpa [sixMul] using hnem.symm

/-- **The tail bound.** Beyond `M` the Möbius series contributes at most
`2/(M+1)` in absolute value, since `|μ| ≤ 1` and `∑_{d > M} d⁻² ≤ 2/(M+1)`. The
constant is explicit rather than an `O()`. -/
theorem moebius_tail_le (M N : ℕ) :
    |∑ d ∈ Finset.Ioo M N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2|
      ≤ 2 / (M + 1) := by
  calc |∑ d ∈ Finset.Ioo M N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ Finset.Ioo M N, |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioo M N, (((d : ℝ)) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 : 1 ≤ d := by
          have := (Finset.mem_Ioo.mp hd).1
          omega
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hsq : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
        rw [abs_div, abs_of_pos hsq, ← one_div, div_le_div_iff₀ hsq hsq]
        nlinarith [abs_moebius_le_one d]
    _ ≤ 2 / (M + 1) := sum_Ioo_inv_sq_le M N

/-- The summand `μ(m)/m²` restricted to the naturals coprime to `6`. -/
noncomputable def coprimeSummand (m : {m : ℕ // Nat.Coprime m 6}) : ℝ :=
  (ArithmeticFunction.moebius m.val : ℝ) / (m.val : ℝ) ^ 2

/-- **`lem_euler_prod`.** `∑_{(m,6)=1} μ(m)/m² = 9/π²`.

Equivalently, the Euler product `∏_{p ≥ 5} (1 - p⁻²) = 9/π²`, reached here
without any Euler-product machinery: every square-free `n` factors uniquely as
`n = e * m` with `e ∣ 6` and `gcd (m, 6) = 1` (`exists_six_decomp`,
`six_part_unique`), the two factors are coprime so `μ` splits
(`coprime_of_dvd_six`), and reindexing the full series along that decomposition
gives

`6/π² = (∑_{e ∣ 6} μ(e)/e²) * (∑_{(m,6)=1} μ(m)/m²) = (2/3) * S`,

whence `S = 9/π²`. -/
@[pz_tag "lem_euler_prod"]
theorem coprime_moebius_tsum :
    ∑' m : {m : ℕ // Nat.Coprime m 6}, coprimeSummand m = 9 / Real.pi ^ 2 := by
  classical
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  -- the full series, as a `HasSum`
  have hfull : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2)
      (6 / Real.pi ^ 2) := by
    have h := summable_moebius_div_sq.hasSum
    rwa [moebius_tsum_real] at h
  -- reindex along the decomposition
  have hcomp : HasSum
      ((fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) ∘ sixMul)
      (6 / Real.pi ^ 2) :=
    (sixMul_injective.hasSum_iff
      (fun x hx => moebius_div_sq_eq_zero_of_notMem_range hx)).mpr hfull
  -- the reindexed summand factors
  have hfac : ∀ p : SixIdx,
      ((fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) ∘ sixMul) p
        = ((ArithmeticFunction.moebius p.1.val : ℝ) / (p.1.val : ℝ) ^ 2)
          * coprimeSummand p.2 := by
    rintro ⟨⟨e, he⟩, ⟨m, hm⟩⟩
    have hd : e ∣ 6 := (Nat.mem_divisors.mp he).1
    have hcop : Nat.Coprime e m := coprime_of_dvd_six hd hm
    simp only [Function.comp_apply, sixMul, coprimeSummand]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    push_cast
    ring
  -- so the product-indexed sum splits
  have hsummable : Summable
      (fun p : SixIdx => ((ArithmeticFunction.moebius p.1.val : ℝ) / (p.1.val : ℝ) ^ 2)
        * coprimeSummand p.2) := by
    have := hcomp.summable
    rwa [funext hfac] at this
  have htot : ∑' p : SixIdx, ((ArithmeticFunction.moebius p.1.val : ℝ) / (p.1.val : ℝ) ^ 2)
      * coprimeSummand p.2 = 6 / Real.pi ^ 2 := by
    have := hcomp.tsum_eq
    rwa [funext hfac] at this
  -- split the product sum, pull the constant out of the inner sum
  rw [hsummable.tsum_prod] at htot
  have hinner : ∀ e : ↥(Nat.divisors 6),
      ∑' m : {m : ℕ // Nat.Coprime m 6},
          ((ArithmeticFunction.moebius e.val : ℝ) / (e.val : ℝ) ^ 2) * coprimeSummand m
        = ((ArithmeticFunction.moebius e.val : ℝ) / (e.val : ℝ) ^ 2)
          * ∑' m : {m : ℕ // Nat.Coprime m 6}, coprimeSummand m := by
    intro e
    exact tsum_mul_left
  rw [tsum_congr hinner, tsum_fintype, ← Finset.sum_mul] at htot
  -- the finite factor is `2/3`
  have hfactor : ∑ e : ↥(Nat.divisors 6),
      (ArithmeticFunction.moebius e.val : ℝ) / (e.val : ℝ) ^ 2 = 2 / 3 := by
    rw [← moebius_factor_six_real]
    exact Finset.sum_coe_sort (Nat.divisors 6)
      (fun e => (ArithmeticFunction.moebius e : ℝ) / (e : ℝ) ^ 2)
  rw [hfactor] at htot
  -- `(2/3) * S = 6/π²`
  have hS : (2 / 3 : ℝ) * ∑' m : {m : ℕ // Nat.Coprime m 6}, coprimeSummand m
      = 6 / Real.pi ^ 2 := htot
  field_simp at hS ⊢
  linarith [hS]

end PartitionZheng
