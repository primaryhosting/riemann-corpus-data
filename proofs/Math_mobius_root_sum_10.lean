import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- For a primitive `n`-th root of unity `ζ`, the finset of primitive `n`-th roots of unity is
the image of the residues coprime to `n` under `i ↦ ζ ^ i`. -/
lemma primitiveRoots_eq_image_pow {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    {ζ : R} {n : ℕ} [NeZero n] (h : IsPrimitiveRoot ζ n) :
    primitiveRoots n R = ((range n).filter (fun i => Nat.Coprime i n)).image (fun i => ζ ^ i) := by
  ext x
  rw [mem_primitiveRoots (NeZero.pos n), h.isPrimitiveRoot_iff]
  simp only [mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, hi, hc, rfl⟩; exact ⟨i, ⟨hi, hc⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hc⟩, rfl⟩; exact ⟨i, hi, hc, rfl⟩

/-- The Möbius function at `10` equals `1`. -/
lemma moebius_ten : (ArithmeticFunction.moebius 10 : ℤ) = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- The sum of the primitive 10-th roots of unity in `ℂ` equals `μ 10`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (ArithmeticFunction.moebius 10 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 10 :=
    ⟨_, Complex.isPrimitiveRoot_exp 10 (by norm_num)⟩
  have hmu : (ArithmeticFunction.moebius 10 : ℂ) = 1 := by
    exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) moebius_ten
  have h10 : ζ ^ 10 = 1 := hζ.pow_eq_one
  have h5ne : ζ ^ 5 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h2ne : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h5 : ζ ^ 5 = -1 := by
    have hfac : (ζ ^ 5 - 1) * (ζ ^ 5 + 1) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h5ne
    · linear_combination h
  have hne : ζ + 1 ≠ 0 := by
    intro h
    exact h2ne (by linear_combination (ζ - 1) * h)
  have hq : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
    have hprod : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by linear_combination h5
    exact (mul_eq_zero.1 hprod).resolve_left hne
  have hset : ((range 10).filter (fun i => Nat.Coprime i 10)) = ({1, 3, 7, 9} : Finset ℕ) := by
    decide
  rw [hmu, primitiveRoots_eq_image_pow hζ, hset,
    Finset.sum_image (g := fun i => ζ ^ i)
      (fun i hi j hj hij => hζ.pow_inj (by simp at hi; omega) (by simp at hj; omega) hij)]
  norm_num [Finset.sum_insert, Finset.mem_insert]
  linear_combination (ζ ^ 2 + ζ ^ 4) * h5 - hq

end Math

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

