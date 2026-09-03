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

/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- **Euler's theorem**, unit form: any unit `a` of `ZMod n` satisfies
`a ^ Nat.totient n = 1`. -/
theorem euler_totient {n : ℕ} (a : ZMod n) (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h : u ^ Nat.totient n = 1 := ZMod.pow_totient u
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

/-- **Euler's theorem**, congruence form: if `a` and `n` are coprime then
`a ^ φ n ≡ 1 [MOD n]`. -/
theorem euler_totient_modEq {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

end NumberTheory

