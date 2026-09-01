/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PartitionZheng.Basic
public import PartitionZheng.Range
public import PartitionZheng.Recover

/-!
# From good discriminants to odd values

This is the counting step. The parity theorem supplies, for each admissible
discriminant `D`, an `m` bounded in terms of the class number and an `n` with
`24 n = D m² + 1` and `p n` odd. For a *good* `D` the bound on `m` makes
`n ≤ Z_H Y`, and `D` is recoverable from `n` as the square-free part of
`24 n - 1`, so distinct good `D` give distinct `n`. Counting the `n` gives the
lower bound on `N_odd`.

## The one external input

`ParityInput` is the statement of the paper's main theorem, odd half only — the
single result this development assumes. It is a `Prop`, not an `axiom`: every
consumer takes it as an explicit hypothesis, so it never enters the kernel's
axiom list and `#print axioms` stays clean on everything below. Only the odd
half is stated; the appendix uses neither the companion bound on the least `m`
giving an even value nor the infinitude claim.

## Main definitions

* `PartitionZheng.ParityInput` — the assumed parity theorem.

## Main results

* `PartitionZheng.Nodd_lower` — `#good(Y,H) ≤ N_odd ⌊Z_H Y⌋`.
-/

@[expose] public section

namespace PartitionZheng

open Real

/-- The parity theorem of Ono and Swaminathan, **odd half only**: for square-free
`D > 1` with `D ≡ 23 [MOD 24]` there are `m` coprime to `6` with
`m ≤ 12 h(D) + 2`, and `n` with `24 n = D m² + 1` and `p n` odd.

This is the development's single external input. Stated as a `Prop` and taken as
a hypothesis by every consumer, so it never becomes an axiom. -/
@[pz_tag "thm_parity_odd"]
def ParityInput : Prop :=
  ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∃ m n : ℕ, 1 ≤ m ∧ Nat.Coprime m 6 ∧
      m ≤ 12 * classNumber (D : ℤ) + 2 ∧ 24 * n = D * m ^ 2 + 1 ∧ Odd (pFun n)

/-- Each good discriminant yields a distinct `n ≤ Z_H Y` with `p n` odd, so
`N_odd` at `Z_H Y` is at least the number of good discriminants. -/
@[pz_tag "lem_Nodd_lower"]
theorem Nodd_lower (hp : ParityInput) {Y H : ℝ} (hY : 0 ≤ Y) :
    (good Y H).card ≤ Nodd ⌊ZH H Y⌋₊ := by
  classical
  -- Choose, for every `D`, the witnesses the parity theorem provides.
  choose! mw nw hm1 hmcop hmle hneq hnodd using hp
  refine Finset.card_le_card_of_injOn nw ?_ ?_
  · -- every good `D` maps into the set `Nodd` counts
    intro D hD
    obtain ⟨hDadm, hDh⟩ := mem_good_iff.mp hD
    obtain ⟨⟨hD2, hDfl⟩, hD24, hDsqf⟩ := mem_admissible.mp hDadm
    have hD1 : 1 < D := by omega
    have hDY : (D : ℝ) ≤ Y := by
      have : ((D : ℝ)) ≤ ((⌊Y⌋₊ : ℝ)) := by exact_mod_cast hDfl
      exact this.trans (Nat.floor_le hY)
    -- the bound on `m`, pushed through the class-number bound
    have hmR : ((mw D : ℕ) : ℝ) ≤ 12 * H * Real.sqrt Y + 2 := by
      have h := hmle D hD1 hDsqf hD24
      have hcast : ((mw D : ℕ) : ℝ)
          ≤ 12 * (classNumber (D : ℤ) : ℝ) + 2 := by exact_mod_cast h
      have : 12 * (classNumber (D : ℤ) : ℝ) ≤ 12 * (H * Real.sqrt Y) := by linarith
      linarith
    have hbound : ((nw D : ℕ) : ℝ) ≤ ZH H Y :=
      nD_le_ZH hY hDY hmR (hneq D hD1 hDsqf hD24)
    have hfloor : nw D ≤ ⌊ZH H Y⌋₊ := Nat.le_floor hbound
    have hodd := hnodd D hD1 hDsqf hD24
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.odd_iff.mp hodd⟩
  · -- injective: `D` is the square-free part of `24 * n - 1`
    intro D hD D' hD' heq
    obtain ⟨hDadm, _⟩ := mem_good_iff.mp (Finset.mem_coe.mp hD)
    obtain ⟨hD'adm, _⟩ := mem_good_iff.mp (Finset.mem_coe.mp hD')
    obtain ⟨⟨hD2, _⟩, hD24, hDsqf⟩ := mem_admissible.mp hDadm
    obtain ⟨⟨hD'2, _⟩, hD'24, hD'sqf⟩ := mem_admissible.mp hD'adm
    have hD1 : 1 < D := by omega
    have hD'1 : 1 < D' := by omega
    have hrec : sqfPart (24 * nw D - 1) = D :=
      recover_disc hDsqf (by have := hm1 D hD1 hDsqf hD24; omega)
        (hneq D hD1 hDsqf hD24)
    have hrec' : sqfPart (24 * nw D' - 1) = D' :=
      recover_disc hD'sqf (by have := hm1 D' hD'1 hD'sqf hD'24; omega)
        (hneq D' hD'1 hD'sqf hD'24)
    rw [← hrec, ← hrec', heq]

end PartitionZheng
