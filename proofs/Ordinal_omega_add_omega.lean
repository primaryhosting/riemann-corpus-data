import Mathlib

/-!
# Omega Add Omega
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_add_omega
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

namespace Ordinal

/-- Ordinal arithmetic: `ω + ω = ω * 2`. -/
theorem omega_add_omega : Ordinal.omega0 + Ordinal.omega0 = Ordinal.omega0 * 2 := by
  have h : (2 : Ordinal) = 1 + 1 := by norm_num
  rw [h, mul_add, mul_one]

end Ordinal

