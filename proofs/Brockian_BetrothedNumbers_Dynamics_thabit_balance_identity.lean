import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.BetrothedNumbers.Dynamics

/-- The divisor-sum function `σ = σ₁`, `σ m = ∑ d ∣ m, d`. -/
def sigmaOne (m : ℕ) : ℕ := ArithmeticFunction.sigma 1 m

lemma sigmaOne_eq_sum (m : ℕ) : sigmaOne m = ∑ d ∈ m.divisors, d := by
  simp [sigmaOne, ArithmeticFunction.sigma_one_apply]

/--
**Thabit balance identity** (subtraction-free form).

Let `m = (2 ^ k - 1) * (p + 2)`, written subtraction-freely as
`m + (p + 2) = 2 ^ k * (p + 2)`, and assume the delivered sigma criterion
`σ m = (2 ^ (k + 1) - 1) * (p + 1)`, again written subtraction-freely as
`σ m + (p + 1) = 2 ^ (k + 1) * (p + 1)`.

Then the balance identity `σ m + 2 ^ (k + 1) = 2 * m + (p + 3)` holds, and
consequently `m` is deficient / perfect / abundant exactly according to how
`p + 3` compares with `2 ^ (k + 1)`.
-/
theorem thabit_balance_identity {k p m : ℕ}
    (hm : m + (p + 2) = 2 ^ k * (p + 2))
    (hsigma : sigmaOne m + (p + 1) = 2 ^ (k + 1) * (p + 1)) :
    sigmaOne m + 2 ^ (k + 1) = 2 * m + (p + 3)
      ∧ (sigmaOne m < 2 * m ↔ p + 3 < 2 ^ (k + 1))
      ∧ (sigmaOne m = 2 * m ↔ p + 3 = 2 ^ (k + 1))
      ∧ (2 * m < sigmaOne m ↔ 2 ^ (k + 1) < p + 3) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [hpow] at hsigma ⊢
  set x : ℕ := 2 ^ k with hx
  set S : ℕ := sigmaOne m with hS
  clear_value x S
  have key : S + 2 * x = 2 * m + (p + 3) := by nlinarith
  refine ⟨key, ?_, ?_, ?_⟩ <;> omega

/-- The hypotheses of `thabit_balance_identity` are satisfiable nontrivially:
`k = 4`, `p = 3`, `m = (2 ^ 4 - 1) * 5 = 75`, with `σ 75 = 124 = (2 ^ 5 - 1) * 4`. -/
lemma thabit_balance_witness :
    (75 : ℕ) + (3 + 2) = 2 ^ 4 * (3 + 2) ∧
      sigmaOne 75 + (3 + 1) = 2 ^ (4 + 1) * (3 + 1) := by
  refine ⟨by norm_num, ?_⟩
  rw [sigmaOne_eq_sum]
  decide

/-- At the witness above, `p + 3 = 6 < 32 = 2 ^ 5`, so the comparison theorem
yields that `75` is deficient. -/
lemma thabit_balance_witness_deficient : sigmaOne 75 < 2 * 75 :=
  (thabit_balance_identity thabit_balance_witness.1 thabit_balance_witness.2).2.1.mpr
    (by norm_num)

end Brockian.BetrothedNumbers.Dynamics

