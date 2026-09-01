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

set_option grind.warning false

namespace Math

open Finset

/-- The sum of the primitive 7-th roots of unity in `ℂ` equals the Möbius function `μ 7 = -1`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  set zz : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7) with hzz
  have hz : IsPrimitiveRoot zz 7 := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  have hcop : ∀ i, 1 ≤ i → i < 7 → Nat.Coprime i 7 := by
    intro i h1 h7
    interval_cases i <;> decide
  have hset : primitiveRoots 7 ℂ = Finset.image (fun i : ℕ => zz ^ i) (Finset.Ico 1 7) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico, mem_primitiveRoots (by norm_num : 0 < 7)]
    constructor
    · intro hx
      rw [hz.isPrimitiveRoot_iff] at hx
      obtain ⟨i, hin, hi, H⟩ := hx
      refine ⟨i, ⟨?_, hin⟩, H⟩
      rcases Nat.eq_zero_or_pos i with rfl | h
      · simp [Nat.Coprime] at hi
      · exact h
    · rintro ⟨i, ⟨hi1, hi7⟩, rfl⟩
      exact hz.pow_of_coprime i (hcop i hi1 hi7)
  rw [hset, Finset.sum_image]
  · have hgeom : ∑ i ∈ Finset.range 7, zz ^ i = 0 := hz.geom_sum_eq_zero (by norm_num)
    have hrange : Finset.range 7 = insert 0 (Finset.Ico 1 7) := by decide +kernel
    rw [hrange, Finset.sum_insert (by simp)] at hgeom
    simp only [pow_zero] at hgeom
    have h7 : (ArithmeticFunction.moebius 7 : ℤ) = -1 :=
      ArithmeticFunction.moebius_apply_prime (by norm_num)
    rw [show ((ArithmeticFunction.moebius 7 : ℤ) : ℂ) = ((-1 : ℤ) : ℂ) by rw [h7]]
    push_cast
    linear_combination hgeom
  · intro i hi j hj h
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    exact hz.pow_inj (by omega) (by omega) h

end Math

