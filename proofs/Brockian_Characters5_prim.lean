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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma prim : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

/-- The sum of all fifth roots of unity vanishes. -/
lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  have h1 : omega ≠ 1 := prim.ne_one (by norm_num)
  rw [geom_sum_eq h1 5, prim.pow_eq_one]
  simp

lemma sum_univ_zmod5 (f : ZMod 5 → ℂ) : ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` is `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  have h : omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    have := sum_omega_pow
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one] at this
    linear_combination this
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by revert a; decide
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · rw [sum_univ_zmod5, if_pos rfl]
    show omega ^ 0 + omega ^ 0 + omega ^ 0 + omega ^ 0 + omega ^ 0 = 5
    norm_num
  · rw [sum_univ_zmod5, if_neg (by decide : (1 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0
    linear_combination h
  · rw [sum_univ_zmod5, if_neg (by decide : (2 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 2 + omega ^ 4 + omega ^ 1 + omega ^ 3 = 0
    linear_combination h
  · rw [sum_univ_zmod5, if_neg (by decide : (3 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 3 + omega ^ 1 + omega ^ 4 + omega ^ 2 = 0
    linear_combination h
  · rw [sum_univ_zmod5, if_neg (by decide : (4 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 4 + omega ^ 3 + omega ^ 2 + omega ^ 1 = 0
    linear_combination h

end Brockian.Characters5

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

