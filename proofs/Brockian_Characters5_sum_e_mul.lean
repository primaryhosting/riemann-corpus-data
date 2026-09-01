/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `exp (2 π i / 5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

/-- `omega` is a primitive fifth root of unity. -/
theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The sum of all fifth powers of `omega` vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

/-- The character sum of `e` over `ZMod 5` vanishes. -/
theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  have h : ∑ x : ZMod 5, e x = ∑ k ∈ Finset.range 5, omega ^ k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => omega ^ k) 5]
    rfl
  rw [h, sum_omega_pow]

/-- Additive-character orthogonality on `ZMod 5`. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [e, ZMod.val_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg ha]
    rw [← sum_e]
    exact Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun x => rfl)

end Characters5
end Brockian

