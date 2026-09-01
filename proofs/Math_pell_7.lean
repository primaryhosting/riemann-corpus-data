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

/-- Pell's equation `x² - 7y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`, hence `x ≠ ±1`): take `x = 8`, `y = 3`. -/
theorem pell_7 : ∃ x y : ℤ, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨8, 3, by norm_num, by norm_num⟩

end Math


