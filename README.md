[![](logo.svg)](https://axiommath.ai/)

# Zheng's Lower Bound on Odd Values of the Partition Function

This is a Lean formalization of Qi-Yang Zheng's square-root lower bound for the number
of odd values of the partition function, the appendix to Ono and Swaminathan's *Parity of
the partition function in quadratic progressions*.

## Main Results

Write `N_odd(X)` for `#{0 ≤ n ≤ X : p(n) is odd}`. Assuming the odd half of
Ono–Swaminathan's parity theorem, and nothing else:

* `liminf_{X → ∞} N_odd(X) / √X ≥ 243 / (64 √6 π⁵)`, the limit inferior over real `X`.
* Equivalently, for every `ε > 0` the ratio `N_odd(X) / √X` is eventually at least
  `243 / (64 √6 π⁵) - ε`.

The class-number average the proof rests on is proved here, not assumed.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on the dependency above. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
