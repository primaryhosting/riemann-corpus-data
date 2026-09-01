import Mathlib

/-- Landau's fourth problem (**OPEN**), recorded as an unproven `def`:
infinitely many `n` have `n ^ 2 + 1` prime. -/
def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

theorem even_of_sq_add_one_prime {n : ℕ} (hn : 1 < n)
    (h : (n ^ 2 + 1).Prime) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exfalso
    have h2 : 2 ∣ n ^ 2 + 1 := by
      have : Odd (n ^ 2) := ho.pow
      exact this.add_one.two_dvd
    have := (Nat.Prime.eq_one_or_self_of_dvd h 2 h2)
    have hlt : 2 < n ^ 2 + 1 := by nlinarith
    rcases this with h1 | h1 <;> omega

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

