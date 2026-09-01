import Mathlib

/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace RequestProject

open Ordinal

/-- `ω ^ 1 = ω`, where `ω = Ordinal.omega0` is the first infinite ordinal.
(In current Mathlib the name `Ordinal.omega` denotes the `ω_` indexing order embedding;
the ordinal `ω` itself is `Ordinal.omega0 = Ordinal.omega 0`.) -/
theorem omega_pow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`, obtained from monotonicity of ordinal exponentiation in the exponent
together with `ω ^ 1 = ω`. -/
theorem omega_le_omega_pow : (omega0 : Ordinal) ≤ omega0 ^ (2 : Ordinal) := by
  have h : (omega0 : Ordinal) ^ (1 : Ordinal) ≤ omega0 ^ (2 : Ordinal) :=
    opow_le_opow_right omega0_pos (by norm_num)
  rwa [omega_pow_one] at h

/-- Restatement of `ω ≤ ω ^ 2` in terms of `Ordinal.omega 0`, the zeroth entry of the
`ω_` hierarchy, which equals `Ordinal.omega0`. -/
theorem omega_le_omega_pow' : Ordinal.omega 0 ≤ Ordinal.omega 0 ^ (2 : Ordinal) := by
  rw [Ordinal.omega_zero]
  exact omega_le_omega_pow

/-- Restatement of `ω ^ 1 = ω` in terms of `Ordinal.omega 0`. -/
theorem omega_pow_one' : Ordinal.omega 0 ^ (1 : Ordinal) = Ordinal.omega 0 :=
  opow_one _

end RequestProject

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

