import Mathlib

def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- Squares are `0` or `1` mod `3`, hence `n ^ 2 + 1` is never divisible by `3`. -/
theorem three_not_dvd_sq_add_one (n : ℕ) : ¬ (3 ∣ n ^ 2 + 1) := by
  intro h
  have hmod : (n ^ 2 + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have hpow : n ^ 2 % 3 = (n % 3) ^ 2 % 3 := Nat.pow_mod n 2 3
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : (n % 3) <;> omega

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

