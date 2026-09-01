/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import PartitionZheng.Meta.Attr

/-!
# Reducedness bounds

Two consequences of `|b| ≤ a ≤ c`, both used to turn the count of reduced
triples of discriminant at most `Y` into a lattice count: the first coefficient
is bounded, and for fixed `a` and `b` the outer coefficient `c` is confined to
an interval of length `(Y + b ^ 2 - 4 * a ^ 2) / (4 * a)`.

The bound on `a` is stated as `3 * a ^ 2 ≤ Y` rather than the source's
`a ≤ sqrt (Y / 3)`. The two are equivalent for `a ≥ 0`, which reducedness
supplies, and the squared form is both what the argument produces and what the
summation over `a` consumes.

## Main results

* `PartitionZheng.three_sq_le_disc` — `3 * a ^ 2 ≤ 4 * a * c - b ^ 2`.
* `PartitionZheng.three_sq_le_of_disc_le` — hence `3 * a ^ 2 ≤ Y`.
* `PartitionZheng.c_upper` — the upper bound on `c`.
* `PartitionZheng.c_interval_length` — the length of the interval for `c`.
-/

@[expose] public section

namespace PartitionZheng

/-- Reducedness gives `4ac - b^2 ≥ 4a^2 - a^2 = 3a^2`. -/
theorem three_sq_le_disc {a b c : ℤ} (hb : |b| ≤ a) (hac : a ≤ c) :
    3 * a ^ 2 ≤ 4 * a * c - b ^ 2 := by
  have ha : 0 ≤ a := le_trans (abs_nonneg b) hb
  have hb2 : b ^ 2 ≤ a ^ 2 := by
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
  nlinarith [mul_le_mul_of_nonneg_left hac (by linarith : (0:ℤ) ≤ 4 * a)]

/-- A reduced triple of discriminant at most `Y` has `3 * a ^ 2 ≤ Y`; for
`a ≥ 0` this is the source's `a ≤ sqrt (Y / 3)`. -/
@[pz_tag "lem_a_bound"]
theorem three_sq_le_of_disc_le {a b c : ℤ} {Y : ℝ} (hb : |b| ≤ a) (hac : a ≤ c)
    (hY : ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y) : 3 * ((a : ℝ)) ^ 2 ≤ Y := by
  have h := three_sq_le_disc hb hac
  have hcast : ((3 * a ^ 2 : ℤ) : ℝ) ≤ ((4 * a * c - b ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast hY
  linarith

/-- For `a ≥ 1`, the condition `4ac - b^2 ≤ Y` is an upper bound on `c`. -/
theorem c_upper {a b c : ℤ} {Y : ℝ} (ha : 1 ≤ a)
    (hY : ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y) :
    (c : ℝ) ≤ (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) := by
  have ha' : (0 : ℝ) < 4 * (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  rw [le_div_iff₀ ha']
  push_cast at hY
  linarith

/-- The admissible `c` for fixed `a ≥ 1` and `b` lie between `a` (reducedness)
and `(Y + b ^ 2) / (4 * a)` (the discriminant bound), an interval of length
`(Y + b ^ 2 - 4 * a ^ 2) / (4 * a)`. -/
@[pz_tag "lem_c_interval"]
theorem c_interval_length {a b : ℤ} {Y : ℝ} (ha : 1 ≤ a) :
    (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) - (a : ℝ)
      = (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
  have ha' : (0 : ℝ) < 4 * (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  field_simp

end PartitionZheng
