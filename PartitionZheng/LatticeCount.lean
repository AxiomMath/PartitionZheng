/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import PartitionZheng.Meta.Attr
public import PartitionZheng.Weight

/-!
# Counting integers of an interval in prescribed residue classes

The lattice count fixes `a` and `b` and confines the outer coefficient `c` to an
interval, intersected with those residue classes modulo `6` that the
discriminant congruence admits. This file supplies the counting step: an
interval with integer endpoints `lo ≤ hi` meets a single class modulo `q` in at
most `(hi - lo) / q + 1` integers, hence a union of `k` classes in at most
`k * (hi - lo) / q + k`.

The count is proved for an arbitrary modulus `q > 0`, since `lem_Dset_card`
needs `q = 24` while the lattice count needs `q = 6`; the mod-`6` statements are
wrappers.

The proof is an explicit injection. On a fixed class the map `c ↦ (c - lo) / q`
is injective, because two members of the class differ by a multiple of `q` and
so share a remainder; and it lands in `Finset.Icc 0 ((hi - lo) / q)`.

The hypothesis `lo ≤ hi` is necessary, not decorative: for `hi < lo` the count
is `0` but `(hi - lo) / q + 1` is negative, so the bound fails. Callers whose
interval may be empty case-split before applying these.

Fixing `a` and `b`, `card_c_le` then assembles the two constraints into a bound
on the number of admissible outer coefficients, in terms of the positive part
`(Y + b² - 4a²)_+` that `def_F` integrates.

## Main definitions

* `PartitionZheng.cClasses` — the classes modulo `6` admitted for `c`.

## Main results

* `PartitionZheng.card_residue_class_Icc_mod` — the single-class count, any `q`.
* `PartitionZheng.card_residue_class_Icc` — its `q = 6` case.
* `PartitionZheng.card_residue_classes_Icc` — the `k`-class count.
* `PartitionZheng.card_c_le` — the count of outer coefficients for fixed `a, b`.
-/

@[expose] public section

namespace PartitionZheng

open Finset

/-- On a fixed residue class modulo `q`, the map `c ↦ (c - lo) / q` is
injective: two members of the class share a remainder, so equal quotients force
equality. `omega` cannot close this directly, because a variable modulus makes
`q * ((c - lo) / q)` a product of two unknowns; the values are rebuilt from
quotient and remainder first. -/
private theorem ediv_injOn_class_mod {q : ℕ} {lo : ℤ} {r : ZMod q} :
    Set.InjOn (fun c : ℤ => (c - lo) / (q : ℤ)) {c : ℤ | (c : ZMod q) = r} := by
  intro c hc c' hc' h
  simp only [Set.mem_ofPred_eq] at hc hc'
  have hmod : c % (q : ℤ) = c' % (q : ℤ) := by
    have hcc : ((c : ZMod q)) = ((c' : ZMod q)) := by rw [hc, hc']
    exact (ZMod.intCast_eq_intCast_iff' c c' q).mp hcc
  have hsub : (c - lo) % (q : ℤ) = (c' - lo) % (q : ℤ) := Int.ModEq.sub hmod rfl
  have hc1 : (q : ℤ) * ((c - lo) / (q : ℤ)) + (c - lo) % (q : ℤ) = c - lo :=
    Int.mul_ediv_add_emod _ _
  have hc2 : (q : ℤ) * ((c' - lo) / (q : ℤ)) + (c' - lo) % (q : ℤ) = c' - lo :=
    Int.mul_ediv_add_emod _ _
  simp only at h
  -- rebuild each value from its quotient and remainder, which now agree
  have heq : c - lo = c' - lo := by rw [← hc1, ← hc2, h, hsub]
  omega

/-- Integer division by `q > 0` is bounded by real division. -/
private theorem ediv_le_real {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ((n / (q : ℤ) : ℤ) : ℝ) ≤ (n : ℝ) / (q : ℝ) := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqr : (q : ℤ) * (n / (q : ℤ)) + n % (q : ℤ) = n := Int.mul_ediv_add_emod _ _
  have hnn : 0 ≤ n % (q : ℤ) := Int.emod_nonneg n (by omega)
  have hz : (q : ℤ) * (n / (q : ℤ)) ≤ n := by omega
  have hz' : (((q : ℤ) * (n / (q : ℤ)) : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hz
  push_cast at hz'
  rw [le_div_iff₀ hqR]
  linarith

/-- **Single class, general modulus.** For `lo ≤ hi` and `q > 0`, the integers
of `Finset.Icc lo hi` lying in one residue class modulo `q` number at most
`(hi - lo) / q + 1`.

`lem_Dset_card` needs this at `q = 24`; the lattice count needs `q = 6`. -/
theorem card_residue_class_Icc_mod {q : ℕ} (hq : 0 < q) {lo hi : ℤ} (hle : lo ≤ hi)
    (r : ZMod q) :
    ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod q) = r)).card : ℝ)
      ≤ ((hi : ℝ) - (lo : ℝ)) / (q : ℝ) + 1 := by
  classical
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqnn : (0 : ℤ) ≤ (hi - lo) / (q : ℤ) := Int.ediv_nonneg (by omega) (by omega)
  have hkey : (((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod q) = r)).card
      ≤ (Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card := by
    refine Finset.card_le_card_of_injOn (fun c => (c - lo) / (q : ℤ)) (fun c hc => ?_) ?_
    · obtain ⟨hmem, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmem
      refine Finset.mem_Icc.mpr ⟨Int.ediv_nonneg (by omega) (by omega), ?_⟩
      exact Int.ediv_le_ediv (by omega) (by omega)
    · intro c hc c' hc' h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc hc'
      exact ediv_injOn_class_mod hc.2 hc'.2 h
  have hcard : (Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card
      = ((hi - lo) / (q : ℤ) + 1).toNat := by
    rw [Int.card_Icc]; congr 1; omega
  have hcast : (((Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card : ℝ))
      = (((hi - lo) / (q : ℤ) : ℤ) : ℝ) + 1 := by
    rw [hcard]
    have h1 : ((((hi - lo) / (q : ℤ) + 1).toNat : ℕ) : ℤ) = (hi - lo) / (q : ℤ) + 1 :=
      Int.toNat_of_nonneg (by omega)
    have h2 : ((((hi - lo) / (q : ℤ) + 1).toNat : ℕ) : ℝ)
        = ((((hi - lo) / (q : ℤ) + 1 : ℤ)) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
    rw [h2]; push_cast; ring
  have hqd : (((hi - lo) / (q : ℤ) : ℤ) : ℝ) ≤ ((hi : ℝ) - (lo : ℝ)) / (q : ℝ) := by
    have hd := ediv_le_real hq (hi - lo)
    push_cast at hd
    linarith
  have hmono : ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod q) = r)).card : ℝ)
      ≤ ((Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card : ℝ) := by exact_mod_cast hkey
  rw [hcast] at hmono
  linarith

/-- **Single class.** The `q = 6` case, which the lattice count uses. -/
theorem card_residue_class_Icc {lo hi : ℤ} (hle : lo ≤ hi) (r : ZMod 6) :
    ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r)).card : ℝ)
      ≤ ((hi : ℝ) - (lo : ℝ)) / 6 + 1 := by
  have h := card_residue_class_Icc_mod (q := 6) (by norm_num) hle r
  norm_num at h
  exact h

/-- **`k` classes.** For `lo ≤ hi`, the integers of `Finset.Icc lo hi` lying in
any of the classes of `S` number at most `#S * ((hi - lo) / 6) + #S`. -/
theorem card_residue_classes_Icc {lo hi : ℤ} (hle : lo ≤ hi) (S : Finset (ZMod 6)) :
    ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) ∈ S)).card : ℝ)
      ≤ S.card * (((hi : ℝ) - (lo : ℝ)) / 6) + S.card := by
  classical
  -- the filter over `S` is the disjoint union of the single-class filters
  have hbi : ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) ∈ S)
      = S.biUnion fun r => ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hmem, hS⟩; exact ⟨_, hS, hmem, rfl⟩
    · rintro ⟨r, hr, hmem, rfl⟩; exact ⟨hmem, hr⟩
  have hdisj : ∀ r ∈ S, ∀ r' ∈ S, r ≠ r' →
      Disjoint ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r)
        ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r') := by
    intro r _ r' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro c hc hc'
    simp only [Finset.mem_filter] at hc hc'
    exact hne (hc.2 ▸ hc'.2 ▸ rfl)
  rw [hbi, Finset.card_biUnion hdisj, Nat.cast_sum]
  calc (∑ r ∈ S, (((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r)).card : ℝ)))
      ≤ ∑ _r ∈ S, (((hi : ℝ) - (lo : ℝ)) / 6 + 1) :=
        Finset.sum_le_sum fun r _ => card_residue_class_Icc hle r
    _ = S.card * (((hi : ℝ) - (lo : ℝ)) / 6) + S.card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The residue classes modulo `6` that the congruence admits for the outer
coefficient, given the inner coefficient `a` and the target class `t`. The
weight of `def_weight` is `2 * #(cClasses a 0) + #(cClasses a 2)`. -/
def cClasses (a : ℤ) (t : ZMod 6) : Finset (ZMod 6) :=
  Finset.univ.filter fun γ => (a : ZMod 6) * γ = t

/-- **The count for fixed `a` and `b`.** Any finite set of outer coefficients
that is bounded below by `a`, bounded above by the discriminant condition, and
confined to the class `t` modulo `6`, has size at most

`#(cClasses a t) * (Y + b² - 4a²)_+ / (4a) / 6 + #(cClasses a t)`.

The target class `t` is a parameter rather than a case split on `b`, so the
caller supplies it from `lem_congruence_ac`: `t = 0` when `gcd (b, 3) = 1` and
`t = 2` when `3 ∣ b`.

The positive part is not a hedge. It is the integrand of `def_F`, so the bound
matches what the area function integrates, and it makes the statement true with
no nonemptiness hypothesis: when `Y + b² - 4a² < 0` the interval of admissible
`c` is empty and the right side is still nonnegative. -/
theorem card_c_le {a b : ℤ} {Y : ℝ} {t : ZMod 6} (ha : 1 ≤ a) (T : Finset ℤ)
    (hlo : ∀ c ∈ T, a ≤ c)
    (hub : ∀ c ∈ T, ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y)
    (hres : ∀ c ∈ T, ((a * c : ℤ) : ZMod 6) = t) :
    (T.card : ℝ)
      ≤ (cClasses a t).card * (max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) / 6)
        + (cClasses a t).card := by
  classical
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha4 : (0 : ℝ) < 4 * (a : ℝ) := by linarith
  have hmaxnn : (0 : ℝ) ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 := le_max_right _ _
  -- the integer ceiling of the discriminant bound
  set hi : ℤ := ⌊(Y + (b : ℝ) ^ 2) / (4 * (a : ℝ))⌋ with hhi
  -- every admissible `c` lies in `Icc a hi` and in one of the classes
  have hsub : T ⊆ (Finset.Icc a hi).filter fun c : ℤ => (c : ZMod 6) ∈ cClasses a t := by
    intro c hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo c hc, ?_⟩, ?_⟩
    · -- `4 a c ≤ Y + b²` gives `c ≤ (Y + b²)/(4a)`, hence `c ≤ ⌊·⌋`
      rw [hhi, Int.le_floor, le_div_iff₀ ha4]
      have h := hub c hc
      push_cast at h
      linarith
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h := hres c hc
      push_cast at h
      exact h
  rcases T.eq_empty_or_nonempty with hemp | ⟨c₀, hc₀⟩
  · -- empty: the right side is nonnegative
    rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · -- nonempty, so `a ≤ hi` and the interval count applies
    have hle : a ≤ hi := le_trans (hlo c₀ hc₀) (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (hsub hc₀)).1).2
    have hcount := card_residue_classes_Icc (lo := a) (hi := hi) hle (cClasses a t)
    have hmono : (T.card : ℝ)
        ≤ ((((Finset.Icc a hi).filter fun c : ℤ => (c : ZMod 6) ∈ cClasses a t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    -- `⌊(Y + b²)/(4a)⌋ - a ≤ (Y + b² - 4a²)_+ / (4a)`
    have hfloor : (hi : ℝ) ≤ (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) := by
      rw [hhi]; exact Int.floor_le _
    have hgap : (hi : ℝ) - (a : ℝ)
        ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) := by
      have hid : (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) - (a : ℝ)
          = (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
        field_simp
      have hstep : (hi : ℝ) - (a : ℝ)
          ≤ (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
        rw [← hid]; linarith
      have hmax : (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ))
          ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) :=
        div_le_div_of_nonneg_right (le_max_left _ _) ha4.le
      linarith
    have hSnn : (0 : ℝ) ≤ ((cClasses a t).card : ℝ) := Nat.cast_nonneg _
    calc (T.card : ℝ)
        ≤ ((((Finset.Icc a hi).filter fun c : ℤ => (c : ZMod 6) ∈ cClasses a t)).card : ℝ) :=
          hmono
      _ ≤ (cClasses a t).card * (((hi : ℝ) - (a : ℝ)) / 6) + (cClasses a t).card := hcount
      _ ≤ (cClasses a t).card
            * (max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) / 6)
          + (cClasses a t).card := by
          have : ((hi : ℝ) - (a : ℝ)) / 6
              ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) / 6 := by
            linarith
          nlinarith [hSnn]

/-- **The fibre of a pair set, as a set of second coordinates.** On the fibre
over `b` the map `p ↦ p.2` is injective, since the first coordinate is pinned.

This is the entry point of the `lem_triple_count_a` assembly:
`Finset.card_eq_sum_card_fiberwise` expresses the pair count as a sum over `b`
of fibre cardinalities, but `card_c_le` takes a `Finset ℤ` of outer
coefficients — not a set of pairs. This converts one to the other without loss. -/
theorem fibre_card_eq_image (b : ℤ) (P : Finset (ℤ × ℤ)) :
    (P.filter fun p => p.1 = b).card
      = ((P.filter fun p => p.1 = b).image Prod.snd).card := by
  classical
  refine (Finset.card_image_of_injOn ?_).symm
  intro p hp q hq h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
  exact Prod.ext_iff.mpr ⟨hp.2.trans hq.2.symm, h⟩

/-- The weight of `def_weight` counted through `cClasses`. -/
theorem weight_eq_cClasses (a : ℤ) :
    2 * (cClasses a 0).card + (cClasses a 2).card
      = 2 * (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 0).card
        + (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 2).card := rfl

/-- `weight a` in the real numbers, through `cClasses`. -/
theorem weight_cast (a : ℤ) :
    ((weight a : ℕ) : ℝ)
      = 2 * ((cClasses a 0).card : ℝ) + ((cClasses a 2).card : ℝ) := by
  unfold weight cClasses
  push_cast
  ring

/-- The classes admitted for `c` at a given `b`: the congruence gives
`a * c ≡ 2 [ZMOD 6]` when `3 ∣ b` and `a * c ≡ 0 [ZMOD 6]` otherwise, by
`lem_congruence_ac`. -/
noncomputable def bClasses (a b : ℤ) : Finset (ZMod 6) :=
  open Classical in
  if 3 ∣ b then cClasses a 2 else cClasses a 0

/-- **The grouping.** A sum over `b` weighted by `#(bClasses a b)` splits into
the two class counts, since `bClasses` depends on `b` only through `3 ∣ b`.

Over the odd residues modulo `6` this is what produces `weight a`: the classes
`b ≡ 1, 5` each contribute `#(cClasses a 0)` and `b ≡ 3` contributes
`#(cClasses a 2)`, and `weight_cast` says `2 * #(cClasses a 0) +
#(cClasses a 2)` is exactly `weight a`. Turning the three class-sums into a
single multiple of `weight a` is the remaining step, and it is an
approximation, not an identity — it needs the sum-to-integral comparison. -/
theorem sum_bClasses_split (a : ℤ) (B : Finset ℤ) (g : ℤ → ℝ) :
    ∑ b ∈ B, ((bClasses a b).card : ℝ) * g b
      = ((cClasses a 2).card : ℝ) * (∑ b ∈ B with (3 ∣ b), g b)
        + ((cClasses a 0).card : ℝ) * (∑ b ∈ B with ¬ (3 ∣ b), g b) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not B (fun b => 3 ∣ b)
        (fun b => ((bClasses a b).card : ℝ) * g b)]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b hb => ?_
    have h3 : (3 : ℤ) ∣ b := (Finset.mem_filter.mp hb).2
    rw [bClasses, ite_eq_left h3]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have h3 : ¬ ((3 : ℤ) ∣ b) := (Finset.mem_filter.mp hb).2
    rw [bClasses, ite_eq_right h3]

end PartitionZheng
