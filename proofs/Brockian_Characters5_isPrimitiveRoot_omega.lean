/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

theorem omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

theorem omega_ne_one : omega ≠ 1 := isPrimitiveRoot_omega.ne_one (by norm_num)

/-- The sum of all fifth powers of `omega` vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  have h : (omega - 1) * ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
    have := geom_sum_mul omega 5
    rw [mul_comm] at this
    rw [this, omega_pow_five, sub_self]
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) omega_ne_one
  · exact h2

theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  have : ∑ x : ZMod 5, e x = ∑ k ∈ Finset.range 5, omega ^ k := by
    show (∑ x : Fin 5, omega ^ (x : ℕ)) = _
    simp [Fin.sum_univ_five, Finset.sum_range_succ]
  rw [this, sum_omega_pow]

theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [e, ZMod.val_zero]
  · rw [if_neg ha]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hbij : Function.Bijective (fun x : ZMod 5 => a * x) :=
      (Equiv.mulLeft₀ a ha).bijective
    have := Fintype.sum_bijective _ hbij (fun x => e (a * x)) e (fun x => rfl)
    rw [this, sum_e]

end Brockian.Characters5

