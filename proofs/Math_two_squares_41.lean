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

namespace Math

/-- The prime 41 is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/
theorem two_squares_41 : Nat.Prime 41 ∧ ∃ a b : ℕ, 41 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 4, 5, by norm_num⟩

end Math

