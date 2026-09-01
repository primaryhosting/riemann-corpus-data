import Mathlib

/-!
# E Eq Std Add Char
Category: Characters
Target: Brockian.Characters5.e_eq_stdAddChar
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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity used for the five-ray wheel. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

local notation "ω" => omega

/-- The bespoke additive character on `ZMod 5`: `e k = ω ^ k.val`. -/
noncomputable def e (k : ZMod 5) : ℂ := ω ^ k.val

/-- The bespoke character equals Mathlib's standard additive character mod `5`. -/
theorem e_eq_stdAddChar (k : ZMod 5) : e k = ZMod.stdAddChar (N := 5) k := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, e, omega, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end Characters5
end Brockian

