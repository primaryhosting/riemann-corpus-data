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

/-- The sum of the primitive `3`-rd roots of unity in `ℂ` equals `μ(3) = -1`. -/
theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = ((ArithmeticFunction.moebius 3 : ℤ) : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hp : IsPrimitiveRoot ζ 3 := by
    have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
    simpa [hζdef] using this
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have h1 : (1 : ℂ) = ζ := by
      have hz : ζ ≠ 0 := hp.ne_zero (by norm_num)
      field_simp at h
      exact h
    exact hp.ne_one (by norm_num) h1.symm
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hp
    · exact (mem_primitiveRoots (by norm_num)).2 (hp.pow_of_coprime 2 (by decide))
  have hcard : (primitiveRoots 3 ℂ).card ≤ ({ζ, ζ ^ 2} : Finset ℂ).card := by
    rw [Complex.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton]
    decide
  have heq : ({ζ, ζ ^ 2} : Finset ℂ) = primitiveRoots 3 ℂ :=
    Finset.eq_of_subset_of_card_le hsub hcard
  rw [← heq, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  have hgs := hp.geom_sum_eq_zero (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hgs
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  push_cast
  linear_combination hgs

end Math

