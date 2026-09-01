/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment because Lean 4 does not allow a
-- module docstring `/-! ... -/` to appear before the `import` commands.)

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math

open Polynomial

/-- The sixth cyclotomic polynomial over `ℂ` has `nextCoeff = -1`. -/
lemma nextCoeff_cyclotomic_six : (cyclotomic 6 ℂ).nextCoeff = -1 := by
  rw [Polynomial.cyclotomic_six]
  have hdeg : (X ^ 2 - X + 1 : ℂ[X]).natDegree = 2 := by
    compute_degree!
  rw [Polynomial.nextCoeff, hdeg]
  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]

/-- **Sum of the primitive 6-th roots of unity.**
The sum of the primitive `6`-th roots of unity in `ℂ` equals the Möbius function `μ(6) = 1`. -/
theorem mobius_root_sum_6 :
    ∑ ζ ∈ primitiveRoots 6 ℂ, ζ = (ArithmeticFunction.moebius 6 : ℂ) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 6)) 6 :=
    Complex.isPrimitiveRoot_exp 6 (by norm_num)
  have hprod := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  have hnext : (∏ μ ∈ primitiveRoots 6 ℂ, (X - C μ)).nextCoeff
      = -∑ μ ∈ primitiveRoots 6 ℂ, μ := Polynomial.prod_X_sub_C_nextCoeff _
  have h : -∑ μ ∈ primitiveRoots 6 ℂ, μ = -1 := by
    rw [← hnext, ← hprod, nextCoeff_cyclotomic_six]
  have hmu : (ArithmeticFunction.moebius 6 : ℤ) = 1 := by
    have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.Coprime 2 3 by norm_num)
    rw [show (6 : ℕ) = 2 * 3 from rfl, hmul,
      ArithmeticFunction.moebius_apply_prime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [neg_inj.mp h, hmu]
  norm_num

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

