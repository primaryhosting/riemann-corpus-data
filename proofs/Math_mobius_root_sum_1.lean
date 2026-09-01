import Mathlib

/-!
# Mobius Root Sum 1
Category: Pure Mathematics
Target: Math.mobius_root_sum_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option autoImplicit false

namespace Math

/-- The sum of the primitive `1`-st roots of unity in `ℂ` equals `μ 1`.

The set of primitive first roots of unity is `{1}` (Mathlib's
`IsPrimitiveRoot.primitiveRoots_one`), and `μ 1 = 1`. -/
theorem mobius_root_sum_1 :
    ∑ z ∈ primitiveRoots 1 ℂ, z = (ArithmeticFunction.moebius 1 : ℂ) := by
  simp [IsPrimitiveRoot.primitiveRoots_one (R := ℂ)]

end Math

