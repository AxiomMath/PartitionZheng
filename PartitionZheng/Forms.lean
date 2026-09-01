/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Int.Interval
public import PartitionZheng.Reduction

/-!
# Binary quadratic forms of a given discriminant

The class number `h D` is *defined* here as the number of reduced primitive
positive-definite binary quadratic forms of discriminant `-D`. Reduced means
`|b| ≤ a ≤ c` together with the boundary condition `0 ≤ b` whenever `|b| = a`
or `a = c`; that condition is what makes the representative of a class unique
(Cox, Theorem 2.8), so without it the count exceeds the class number rather
than computing it.

Taking the correspondence definitionally is what keeps the ideal class group,
Gauss composition and reduction theory out of this development entirely — none
of which Mathlib has.

Only one direction is ever used: the argument needs an upper bound for `h D`,
so it is enough that every class is counted at least once. `classNumber_le`
discards the boundary condition and primitivity together, each of which can
only increase the count.

## Main definitions

* `PartitionZheng.IsReducedTriple` — `|b| ≤ a ≤ c` and `4ac - b² = D`.
* `PartitionZheng.reducedTriples` — the triples of discriminant `-D`.
* `PartitionZheng.reducedTriplesUpTo` — those of discriminant at most `Y`
  in the admissible congruence class.
* `PartitionZheng.reducedForms` — the primitive, boundary-normalised ones.
* `PartitionZheng.classNumber` — `h D`, their number.

## Main results

* `PartitionZheng.reducedTriples_finite` — the triple set is finite.
* `PartitionZheng.classNumber_le` — `h D ≤ #(reducedTriples D)`.
-/

@[expose] public section

namespace PartitionZheng

/-- `[a,b,c]` is a reduced triple of discriminant `-D`: `|b| ≤ a ≤ c` and
`4ac - b² = D`. Positive-definiteness is implied, since `D > 0` and `a ≤ c`
force `a > 0`. -/
def IsReducedTriple (D a b c : ℤ) : Prop :=
  |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = D

/-- `[a,b,c]` is moreover a *form*: primitive, and boundary-normalised so that
each class has exactly one such representative. -/
def IsReducedForm (D a b c : ℤ) : Prop :=
  IsReducedTriple D a b c ∧ Int.gcd (Int.gcd a b) c = 1 ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)

/-- The reduced triples of discriminant `-D`. -/
@[pz_tag "def_triples_disc"]
def reducedTriples (D : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {p | IsReducedTriple D p.1 p.2.1 p.2.2}

/-- The reduced triples of discriminant at most `Y`, in the admissible
congruence class modulo `24`. -/
@[pz_tag "def_triples_upto"]
def reducedTriplesUpTo (Y : ℝ) : Set (ℤ × ℤ × ℤ) :=
  {p | |p.2.1| ≤ p.1 ∧ p.1 ≤ p.2.2 ∧
       0 < 4 * p.1 * p.2.2 - p.2.1 ^ 2 ∧
       ((4 * p.1 * p.2.2 - p.2.1 ^ 2 : ℤ) : ℝ) ≤ Y ∧
       (4 * p.1 * p.2.2 - p.2.1 ^ 2) % 24 = 23}

/-- The reduced primitive forms of discriminant `-D`. -/
@[pz_tag "def_forms"]
def reducedForms (D : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {p | IsReducedForm D p.1 p.2.1 p.2.2}

/-- The class number `h D`, as the number of reduced primitive forms of
discriminant `-D`. -/
@[pz_tag "def_h"]
noncomputable def classNumber (D : ℤ) : ℕ := (reducedForms D).ncard

/-- A reduced triple of positive discriminant has `a ≥ 1`: `a = 0` forces
`b = 0` and then the discriminant is `0`. -/
theorem one_le_a_of_mem {D a b c : ℤ} (hD : 0 < D) (h : IsReducedTriple D a b c) :
    1 ≤ a := by
  obtain ⟨hb, hac, hdisc⟩ := h
  have ha : 0 ≤ a := le_trans (abs_nonneg b) hb
  rcases eq_or_lt_of_le ha with rfl | ha1
  · have hb0 : b = 0 := abs_nonpos_iff.mp hb
    rw [hb0] at hdisc
    norm_num at hdisc
    omega
  · omega

/-- Every reduced triple of discriminant `-D` has all three coefficients in
`[-D, D]`, so the set is finite. -/
theorem reducedTriples_finite {D : ℤ} (hD : 0 < D) : (reducedTriples D).Finite := by
  -- There is no `LocallyFiniteOrder (ℤ × ℤ × ℤ)`, so bound by a product of
  -- interval *sets* rather than an `Icc` of the product.
  have hfin : (Set.Icc (-D) D ×ˢ (Set.Icc (-D) D ×ˢ Set.Icc (-D) D)).Finite :=
    (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  refine hfin.subset ?_
  rintro ⟨a, b, c⟩ hp
  -- Ascribe the type so the projections beta-reduce to `a`, `b`, `c`;
  -- otherwise `omega` sees `(a, b, c).2.1` and `b` as distinct atoms.
  obtain ⟨hb, hac, hdisc⟩ : IsReducedTriple D a b c := hp
  have ha1 : 1 ≤ a := one_le_a_of_mem hD ⟨hb, hac, hdisc⟩
  have hb2 : b ^ 2 ≤ a ^ 2 := by
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
  have h3 : 3 * a ^ 2 ≤ D := by
    have h := three_sq_le_disc hb hac
    omega
  have haD : a ≤ D := by nlinarith [sq_nonneg a, sq_nonneg (a - 1)]
  have hbD : |b| ≤ D := le_trans hb haD
  have hbl : -D ≤ b := neg_le_of_abs_le hbD
  have hbu : b ≤ D := le_of_abs_le hbD
  have hcD : c ≤ D := by nlinarith [sq_nonneg a, sq_nonneg (c - a)]
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

/-- Dropping primitivity and the boundary condition can only increase the
count, so the class number is at most the number of reduced triples. -/
@[pz_tag "lem_h_le_triples"]
theorem classNumber_le {D : ℤ} (hD : 0 < D) :
    classNumber D ≤ (reducedTriples D).ncard := by
  refine Set.ncard_le_ncard ?_ (reducedTriples_finite hD)
  rintro ⟨a, b, c⟩ ⟨htriple, _, _⟩
  exact htriple

end PartitionZheng
