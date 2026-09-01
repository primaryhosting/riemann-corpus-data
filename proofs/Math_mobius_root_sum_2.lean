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

open scoped ArithmeticFunction.Moebius

namespace Math

/-- The sum of the primitive `2`-th roots of unity (in `ℂ`) equals `μ 2 = -1`. -/
theorem mobius_root_sum_2 : ∑ z ∈ primitiveRoots 2 ℂ, z = (μ 2 : ℤ) := by
  have h : primitiveRoots 2 ℂ = {(-1 : ℂ)} := by
    ext z
    simp only [mem_primitiveRoots (by norm_num : 0 < 2), Finset.mem_singleton]
    constructor
    · intro h
      have h2 : z ^ 2 = 1 := h.pow_eq_one
      have h1 : z ≠ 1 := fun hz =>
        h.pow_ne_one_of_pos_of_lt one_ne_zero one_lt_two (by rw [hz]; ring)
      have hz : (z - 1) * (z + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 hz with h3 | h3
      · exact absurd (by linear_combination h3) h1
      · linear_combination h3
    · rintro rfl
      exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  rw [h, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  simp

end Math

