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

import Mathlib

/-- Landau's problem: there are infinitely many primes of the form `n^2 + 1`. -/
def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- Consecutive values of `n^2 + 1` are almost coprime: any common divisor divides `5`.
The key identity is `(2n+3)(n^2+1) - (2n-1)((n+1)^2+1) = 5`. -/
theorem gcd_sq_add_one_succ_dvd_five (n : ℕ) : Nat.gcd (n ^ 2 + 1) ((n + 1) ^ 2 + 1) ∣ 5 := by
  set d := Nat.gcd (n ^ 2 + 1) ((n + 1) ^ 2 + 1) with hd
  have h1 : (d : ℤ) ∣ ((n : ℤ) ^ 2 + 1) := by
    have := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left (n ^ 2 + 1) ((n + 1) ^ 2 + 1))
    push_cast at this
    simpa [hd] using this
  have h2 : (d : ℤ) ∣ (((n : ℤ) + 1) ^ 2 + 1) := by
    have := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right (n ^ 2 + 1) ((n + 1) ^ 2 + 1))
    push_cast at this
    simpa [hd] using this
  have h5 : (d : ℤ) ∣ 5 := by
    have h := dvd_sub (h1.mul_left (2 * (n : ℤ) + 3)) (h2.mul_left (2 * (n : ℤ) - 1))
    have e : (2 * (n : ℤ) + 3) * ((n : ℤ) ^ 2 + 1)
        - (2 * (n : ℤ) - 1) * (((n : ℤ) + 1) ^ 2 + 1) = 5 := by ring
    rwa [e] at h
  exact_mod_cast h5

