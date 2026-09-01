import Mathlib
/-!
# Fermat Little
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.fermat_little
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

namespace NumberTheory

/-- **Fermat's little theorem**, stated over `ZMod p`: for a prime `p` and any
`x : ZMod p`, we have `x ^ p = x`. -/
theorem fermat_little (p : ℕ) [Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x :=
  ZMod.pow_card x

end NumberTheory

