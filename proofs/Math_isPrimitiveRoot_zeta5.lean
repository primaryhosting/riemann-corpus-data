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

/-
/-!
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open Finset Complex

namespace Math

/-- A fixed primitive 5-th root of unity in `ℂ`. -/
noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

theorem isPrimitiveRoot_zeta5 : IsPrimitiveRoot zeta5 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The primitive 5-th roots of unity are exactly `ζ^1, …, ζ^4`. -/
theorem primitiveRoots_five_eq :
    primitiveRoots 5 ℂ = (Finset.Ico 1 5).image (fun i => zeta5 ^ i) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 5), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := isPrimitiveRoot_zeta5.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hix⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · exact absurd (by rw [← hix, h, pow_zero]) (hx.ne_one (by norm_num))
    · exact h
  · rintro ⟨i, ⟨hi1, hi5⟩, rfl⟩
    refine isPrimitiveRoot_zeta5.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive 5-th roots of unity equals `μ 5`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = (ArithmeticFunction.moebius 5 : ℂ) := by
  have hinj : Set.InjOn (fun i => zeta5 ^ i) (Finset.Ico 1 5 : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact isPrimitiveRoot_zeta5.pow_inj (by omega) (by omega) hab
  have hgeom : ∑ i ∈ Finset.range 5, zeta5 ^ i = 0 :=
    isPrimitiveRoot_zeta5.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 5, zeta5 ^ i
      = 1 + ∑ i ∈ Finset.Ico 1 5, zeta5 ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num)]
    simp
  have hmob : (ArithmeticFunction.moebius 5 : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [primitiveRoots_five_eq, Finset.sum_image (fun a ha b hb h => hinj ha hb h), hmob]
  rw [hsplit] at hgeom
  linear_combination hgeom

end Math

