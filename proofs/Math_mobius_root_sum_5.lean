/-
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Polynomial

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The number of primitive `5`-th roots of unity in `ℂ` is `4`. -/
private lemma card_primitiveRoots_five : (primitiveRoots 5 ℂ).card = 4 := by
  rw [Complex.card_primitiveRoots]
  decide

/-- The coefficient of `X ^ 3` in the fifth cyclotomic polynomial is `1`. -/
private lemma coeff_cyclotomic_five : ((cyclotomic 5 ℂ).coeff 3) = 1 := by
  rw [cyclotomic_prime]
  simp [Finset.sum_range_succ, coeff_one, coeff_X_pow, coeff_X]

/-- The sum of the primitive `5`-th roots of unity equals `μ 5 = -1`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = (ArithmeticFunction.moebius 5 : ℂ) := by
  have hprod : cyclotomic 5 ℂ = ∏ z ∈ primitiveRoots 5 ℂ, (X - C z) :=
    cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp 5 (by norm_num))
  have hcoeff :
      (∏ z ∈ primitiveRoots 5 ℂ, (X - C (id z))).coeff ((primitiveRoots 5 ℂ).card - 1)
        = -∑ z ∈ primitiveRoots 5 ℂ, id z :=
    Polynomial.prod_X_sub_C_coeff_card_pred _ _ (by rw [card_primitiveRoots_five]; norm_num)
  rw [card_primitiveRoots_five] at hcoeff
  simp only [id] at hcoeff
  rw [← hprod] at hcoeff
  norm_num [coeff_cyclotomic_five] at hcoeff
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  push_cast
  linear_combination hcoeff

end Math

