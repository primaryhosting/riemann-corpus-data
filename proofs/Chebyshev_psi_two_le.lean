/-
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
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

namespace Chebyshev

open ArithmeticFunction

/-- The second Chebyshev function at `4`: the sum of the von Mangoldt function
`Λ(n)` over `n ∈ {1, 2, 3, 4}` equals `log 12`
(since `Λ 1 = 0`, `Λ 2 = log 2`, `Λ 3 = log 3`, `Λ 4 = log 2`). -/
theorem psi_two_le : ∑ n ∈ Finset.Icc 1 4, Λ n = Real.log 12 := by
  have h1 : Λ 1 = 0 := by simp
  have h2 : Λ 2 = Real.log 2 := by
    simpa using vonMangoldt_apply_prime Nat.prime_two
  have h3 : Λ 3 = Real.log 3 := by
    simpa using vonMangoldt_apply_prime Nat.prime_three
  have h4 : Λ 4 = Real.log 2 := by
    have h : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h, vonMangoldt_apply_pow (two_ne_zero), vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  rw [show ((12 : ℝ)) = 2 * 2 * 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  simp [h1, h2, h3, h4]
  ring

end Chebyshev

