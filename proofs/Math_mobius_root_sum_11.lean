import Mathlib

/-!
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The sum of the primitive 11-th roots of unity in `ℂ` equals `μ(11) = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  have hp : Nat.Prime 11 := by norm_num
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 11 :=
    ⟨_, Complex.isPrimitiveRoot_exp 11 (by norm_num)⟩
  have key : ∑ i ∈ (Finset.range 11).erase 0, ζ ^ i = ∑ z ∈ primitiveRoots 11 ℂ, z := by
    refine Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_erase, Finset.mem_range] at hi
      rw [mem_primitiveRoots (by norm_num)]
      refine hζ.pow_of_coprime i ?_
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
      exact hi.1 (Nat.eq_zero_of_dvd_of_lt hd hi.2)
    · intro i hi j hj H
      rw [Finset.mem_erase, Finset.mem_range] at hi hj
      exact hζ.pow_inj hi.2 hj.2 H
    · intro ξ hξ
      rw [mem_primitiveRoots (by norm_num), hζ.isPrimitiveRoot_iff] at hξ
      obtain ⟨i, hin, hi, H⟩ := hξ
      refine ⟨i, ?_, H⟩
      rw [Finset.mem_erase, Finset.mem_range]
      refine ⟨?_, hin⟩
      rintro rfl
      simp [Nat.coprime_zero_left] at hi
    · intro i _; rfl
  rw [← key, Finset.sum_erase_eq_sub (by simp), hζ.geom_sum_eq_zero (by norm_num),
    ArithmeticFunction.moebius_apply_prime hp]
  norm_num

end Math

