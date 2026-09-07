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

/-- The sum of the primitive 11-th roots of unity (in `ℂ`) equals `μ 11 = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  have hzeta : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 11)) 11 :=
    Complex.isPrimitiveRoot_exp 11 (by norm_num)
  have hset : primitiveRoots 11 ℂ =
      (Finset.Ico 1 11).image (fun i : ℕ => Complex.exp (2 * Real.pi * Complex.I / 11) ^ i) := by
    ext x
    simp only [mem_primitiveRoots (by norm_num : 0 < 11), Finset.mem_image, Finset.mem_Ico]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := hzeta.eq_pow_of_pow_eq_one hx.pow_eq_one
      refine ⟨i, ⟨?_, hi⟩, rfl⟩
      rcases Nat.eq_zero_or_pos i with rfl | h
      · simp only [pow_zero] at hx
        exact absurd (hx.unique (IsPrimitiveRoot.one_right_iff.2 rfl)) (by norm_num)
      · exact h
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      refine hzeta.pow_of_coprime i ?_
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2
        (fun h => by have := Nat.le_of_dvd h1 h; omega)
  have hinj : Set.InjOn (fun i : ℕ => (Complex.exp (2 * Real.pi * Complex.I / 11)) ^ i)
      (Finset.Ico 1 11) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hzeta.pow_inj (by omega) (by omega) hab
  rw [hset, Finset.sum_image (fun a ha b hb => hinj ha hb)]
  have h0 := hzeta.geom_sum_eq_zero (by norm_num)
  have hr : Finset.range 11 = insert 0 (Finset.Ico 1 11) := by decide +kernel
  rw [hr, Finset.sum_insert (by simp)] at h0
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  push_cast
  linear_combination h0

end Math

#print axioms Math.mobius_root_sum_11

