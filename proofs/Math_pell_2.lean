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

/-- Pell's equation `x² - 2·y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`, hence `x ≠ ±1`): for instance `(x, y) = (3, 2)`. -/
theorem pell_2 : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 := by
  refine ⟨3, 2, by norm_num, by norm_num⟩

end Math

