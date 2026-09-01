import Mathlib

/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
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

/-- Key intermediate lemma: `ω ^ 1 = ω`.
(In current Mathlib the ordinal `ω` is named `Ordinal.omega0`; `Ordinal.omega` is the
`ω_` indexing function, so the statements below are phrased with `omega0`.) -/
theorem omega_pow_one : omega0 ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`, obtained from `ω ^ 1 = ω` and monotonicity of `ω ^ ·`. -/
theorem omega_le_omega_pow : omega0 ≤ omega0 ^ (2 : Ordinal) := by
  calc omega0 = omega0 ^ (1 : Ordinal) := omega_pow_one.symm
    _ ≤ omega0 ^ (2 : Ordinal) := opow_le_opow_right omega0_pos (by norm_num)

end Ordinal

