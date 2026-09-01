/-
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
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

namespace Zeta23Redux.LinAlg

/-- Montgomery's integrality step: for every natural number `m`, `2 * m ≤ m ^ 2 + 1`,
which is the shadow of `(m - 1) ^ 2 ≥ 0`. -/
theorem integrality_shadow (m : ℕ) : 2 * m ≤ m ^ 2 + 1 := by
  nlinarith [sq_nonneg ((m : ℤ) - 1), sq_nonneg m]

/-- Integer reformulation: `(m : ℤ) ^ 2 ≥ 2 * m - 1` for every natural number `m`. -/
theorem integrality_shadow_int (m : ℕ) : ((m : ℤ)) ^ 2 ≥ 2 * (m : ℤ) - 1 := by
  nlinarith [sq_nonneg ((m : ℤ) - 1)]

end Zeta23Redux.LinAlg

