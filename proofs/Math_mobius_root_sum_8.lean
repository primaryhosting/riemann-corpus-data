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

open Finset

/-- Any negation of a primitive 8-th root of unity is again a primitive 8-th root of unity.
Indeed, if `a` is primitive of order 8 then `a ^ 4 = -1`, so `-a = a ^ 5` and `5` is coprime
to `8`. -/
theorem neg_isPrimitiveRoot_eight (a : ℂ) (h : IsPrimitiveRoot a 8) :
    IsPrimitiveRoot (-a) 8 := by
  have h4 : a ^ 4 = -1 := by
    have h8 : a ^ 4 * a ^ 4 = 1 := by
      rw [← pow_add]; exact h.pow_eq_one
    rcases mul_self_eq_one_iff.mp h8 with h1 | h1
    · exact absurd h1 (h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
    · exact h1
  have hna : -a = a ^ 5 := by
    rw [pow_succ, h4]; ring
  rw [hna]
  exact h.pow_of_coprime 5 (by decide)

/-- The sum of the primitive 8-th roots of unity in `ℂ` equals `μ 8` (which is `0`, since
`8 = 2 ^ 3` is not squarefree). The primitive 8-th roots come in pairs `ζ, -ζ`. -/
theorem mobius_root_sum_8 :
    ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hmu : (ArithmeticFunction.moebius 8 : ℂ) = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)]
    norm_num
  rw [hmu]
  refine Finset.sum_involution (fun a _ => -a) (fun a _ => by ring) ?_ ?_ (fun a _ => neg_neg a)
  · intro a _ ha
    simpa using fun h => ha (by linear_combination -h / 2 : a = 0)
  · intro a ha
    rw [mem_primitiveRoots (by norm_num)] at ha ⊢
    exact neg_isPrimitiveRoot_eight a ha

end Math

