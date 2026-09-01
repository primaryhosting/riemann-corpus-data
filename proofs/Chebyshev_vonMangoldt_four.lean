import Mathlib
/-!
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction Finset

namespace Chebyshev

/-- `Λ 4 = Real.log 2`, since `4 = 2 ^ 2`. -/
lemma vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, vonMangoldt_apply_pow (two_ne_zero), vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The second Chebyshev function at `4`:
`ψ(4) = Λ 1 + Λ 2 + Λ 3 + Λ 4 = log 2 + log 3 + log 2 = log 12`. -/
theorem psi_two_le : ∑ n ∈ Finset.Icc 1 4, Λ n = Real.log 12 := by
  have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [hIcc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [vonMangoldt_apply_one, vonMangoldt_apply_prime Nat.prime_two,
    vonMangoldt_apply_prime Nat.prime_three, vonMangoldt_four]
  have h12 : (12 : ℝ) = 2 * 3 * 2 := by norm_num
  rw [h12, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  push_cast
  ring

end Chebyshev

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

