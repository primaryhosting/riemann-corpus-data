import Mathlib

/-!
# Heine Borel Interval
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.heine_borel_interval
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

namespace Topology

/-- **Heine–Borel for a closed bounded interval**: for real numbers `a` and `b`, the closed
interval `Set.Icc a b` is compact.  This is Mathlib's `isCompact_Icc`. -/
theorem heine_borel_interval (a b : ℝ) : IsCompact (Set.Icc a b) :=
  isCompact_Icc

end Topology

