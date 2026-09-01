/-
# Freiman Two A
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.freiman_two_A
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

namespace AdditiveComb

/-- **Basic doubling lower bound.** For a finite nonempty set `A` of integers, the sumset
`A + A` has at least `2 * |A| - 1` elements. -/
theorem freiman_two_A (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by
  have h := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hA
  omega

end AdditiveComb

