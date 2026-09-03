import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
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

open Polynomial

/-- The sum of the primitive `6`-th roots of unity in `ℂ` equals `μ 6` (which is `1`). -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 6 = 1 := by
    have h : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  -- there are exactly `φ 6 = 2` primitive sixth roots of unity
  have hcard : (primitiveRoots 6 ℂ).card = 2 := by
    rw [Complex.card_primitiveRoots]; decide +kernel
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hcard
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 6 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 6), Complex.isPrimitiveRoot_exp 6 (by norm_num)⟩
  -- the 6th cyclotomic polynomial factors as `(X - a) (X - b)`
  have hprod : cyclotomic 6 ℂ = (X - C a) * (X - C b) := by
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, hs, Finset.prod_pair hab]
  -- and it equals `X ^ 2 - X + 1`, so `a + b = 1`
  have h1 : (cyclotomic 6 ℂ).coeff 1 = -1 := by
    rw [cyclotomic_six]; simp [coeff_one]
  have h2 : ((X - C a) * (X - C b) : ℂ[X]).coeff 1 = -(a + b) := by
    have h3 : ((X - C a) * (X - C b) : ℂ[X]) = X ^ 2 - C (a + b) * X + C (a * b) := by
      rw [C_add, C_mul]; ring
    rw [h3]; simp
  rw [hprod, h2] at h1
  rw [hs, Finset.sum_pair hab, hmu]
  push_cast
  linear_combination -h1

end Math

