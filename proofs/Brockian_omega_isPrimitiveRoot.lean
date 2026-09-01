import Mathlib

/-!
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- The fifth root of unity `ω = exp(2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, given by `e j = ω ^ j.val`. -/
noncomputable def e (j : ZMod 5) : ℂ := omega ^ j.val

/-- `ω` is a *primitive* fifth root of unity (Mathlib: `Complex.isPrimitiveRoot_exp`). -/
theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using h

/-- `ω ^ 5 = 1`. -/
theorem omega_pow_five : omega ^ 5 = 1 := omega_isPrimitiveRoot.pow_eq_one

/-- `ω ≠ 1`, so the character `e` is nontrivial. -/
theorem omega_ne_one : omega ≠ 1 := omega_isPrimitiveRoot.ne_one (by norm_num)

/-- `e` turns addition in `ZMod 5` into multiplication in `ℂ`. -/
theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  rw [e, e, e, ← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (j.val + k.val) 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

/-- `e 0 = 1`. -/
theorem e_zero : e 0 = 1 := by
  simp [e]

/-- `e 1 = ω`. -/
theorem e_one : e 1 = omega := by
  have h : (1 : ZMod 5).val = 1 := by decide
  simp [e, h]

/-- The character `e` is nontrivial: it is not identically `1`. -/
theorem e_ne_one : e 1 ≠ 1 := by
  rw [e_one]
  exact omega_ne_one

end Characters5
end Brockian

