/-
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/`: Lean 4 does not allow a module
-- docstring before `import` commands.)

import Mathlib

open Finset Pointwise

namespace AdditiveComb

/-- **Sumset lower bound over the integers** (the Cauchy–Davenport analogue over `ℤ`, i.e.
Freiman's lemma base case): for finite nonempty sets `A B : Finset ℤ`,
`#A + #B - 1 ≤ #(A + B)` (subtraction in `ℕ`).

This follows from Mathlib's `cauchy_davenport_add_of_linearOrder_isCancelAdd`, the
Cauchy–Davenport theorem for linearly ordered cancellative additive semigroups. -/
theorem sumset_lower_bound {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card :=
  cauchy_davenport_add_of_linearOrder_isCancelAdd hA hB

end AdditiveComb

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

