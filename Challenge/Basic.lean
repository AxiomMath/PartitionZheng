module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Set.Card
public import Mathlib.Order.LiminfLimsup

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statement that this repository proves.

-/

@[expose] public section

namespace PartitionZheng

/-- The partition function `p n`: the number of partitions of `n`. -/
def pFun (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `Nodd X` counts the integers `0 ≤ n ≤ X` whose partition number is odd,
written `N_odd(X)` in the source. -/
def Nodd (X : ℕ) : ℕ :=
  ((Finset.range (X + 1)).filter fun n => pFun n % 2 = 1).card

/-- `[a,b,c]` is a reduced triple of discriminant `-D`: `|b| ≤ a ≤ c` and
`4ac - b² = D`. -/
def IsReducedTriple (D a b c : ℤ) : Prop :=
  |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = D

/-- `[a,b,c]` is moreover a *form*: primitive, and boundary-normalised. The
normalisation is what makes the reduced representative unique. -/
def IsReducedForm (D a b c : ℤ) : Prop :=
  IsReducedTriple D a b c ∧ Int.gcd (Int.gcd a b) c = 1 ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)

/-- The reduced primitive forms of discriminant `-D`. -/
def reducedForms (D : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {p | IsReducedForm D p.1 p.2.1 p.2.2}

/-- The class number `h(-D)`, the number of reduced primitive positive-definite binary
quadratic forms of discriminant `-D`. Taking the form count as the definition is what
makes it elementary; it agrees with the class number of `ℚ(√-D)` by Cox, Theorem 2.8. -/
noncomputable def classNumber (D : ℤ) : ℕ := (reducedForms D).ncard

/-! ## The parity theorem as hypothesis

K. Ono and A. Swaminathan, *Parity of the partition function in quadratic progressions*
(appendix by Qi-Yang Zheng), **Theorem 1**, the odd half together with its bound
`m_odd ≤ 12 h(-D) + 2`. This is the one external input the project assumes.

Only the odd half is stated. The companion bound on `m_even` and the claim that both
parities occur infinitely often are not used, so assuming them would assume strictly
more than the proof consumes. -/

/-- **Ono–Swaminathan, Theorem 1, odd half.** For square-free `D > 1` with
`D ≡ 23 (mod 24)` there is an `m` coprime to `6` with `m ≤ 12 h(-D) + 2`, and an `n`
with `24 n = D m² + 1` and `p n` odd. -/
def ParityInput : Prop :=
  ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∃ m n : ℕ, 1 ≤ m ∧ Nat.Coprime m 6 ∧
      m ≤ 12 * classNumber (D : ℤ) + 2 ∧ 24 * n = D * m ^ 2 + 1 ∧ Odd (pFun n)

end PartitionZheng

namespace PartitionZheng.Challenge

/-- **`thm_main` — Zheng's lower bound.** `N_odd(X)` is at least `243/(64√6 π⁵)`
times `√X` in the limit inferior, given the parity theorem:

`liminf_{X → ∞} N_odd(X) / √X ≥ 243 / (64 √6 π⁵)`.

The limit inferior is over real `X` and is formed in `EReal`. -/
theorem thm_main (hp : ParityInput) :
    ((243 / (64 * Real.sqrt 6 * Real.pi ^ 5) : ℝ) : EReal) ≤
      Filter.liminf (fun X : ℝ => (((Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X : ℝ) : EReal))
        Filter.atTop :=
  sorry

end PartitionZheng.Challenge
