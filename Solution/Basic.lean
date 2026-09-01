module

public import PartitionZheng.Main

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace PartitionZheng.Challenge

/-- **`thm_main` — Zheng's lower bound.** `N_odd(X)` is at least `243/(64√6 π⁵)`
times `√X` in the limit inferior, given the parity theorem:

`liminf_{X → ∞} N_odd(X) / √X ≥ 243 / (64 √6 π⁵)`.

The limit inferior is over real `X` and is formed in `EReal`. -/
theorem thm_main (hp : ParityInput) :
    ((243 / (64 * Real.sqrt 6 * Real.pi ^ 5) : ℝ) : EReal) ≤
      Filter.liminf (fun X : ℝ => (((Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X : ℝ) : EReal))
        Filter.atTop :=
  liminf_Nodd_ge_const hp

end PartitionZheng.Challenge
