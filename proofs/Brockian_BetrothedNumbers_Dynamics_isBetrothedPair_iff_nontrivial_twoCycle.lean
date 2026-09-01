/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

namespace Dynamics

/-- The *partner* (or quasi-aliquot) function: `partner n = σ₁(n) - n - 1`, the sum of the
"nontrivial" divisors of `n` (all divisors except `n` itself and `1`).  Subtraction is
truncated natural subtraction. -/
def partner (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n - 1

/-- `(m, n)` is a *betrothed* (quasi-amicable) pair when `m` and `n` are distinct positive
integers with `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1

/-- `(m, n)` is a *nontrivial 2-cycle* of `partner` when `m` and `n` are distinct positive
integers swapped by `partner`. -/
def IsNontrivialTwoCycle (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m

/-- **Characterization of betrothed pairs.**  A pair of naturals is a betrothed
(quasi-amicable) pair exactly when it is a positive nontrivial 2-cycle of the partner map
`partner n = σ₁(n) - n - 1`. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔ IsNontrivialTwoCycle m n := by
  unfold IsBetrothedPair IsNontrivialTwoCycle partner
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> omega
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> omega

/-- The classical smallest betrothed pair `(48, 75)`. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

end Dynamics

end BetrothedNumbers

end Brockian

