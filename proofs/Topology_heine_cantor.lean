import Mathlib

/-!
# Heine Cantor
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.heine_cantor
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

namespace Topology

/-- **Heine–Cantor theorem**: a continuous map from a compact uniform space to a
uniform space is uniformly continuous. -/
theorem heine_cantor {X : Type*} {Y : Type*} [UniformSpace X] [UniformSpace Y]
    [CompactSpace X] {f : X → Y} (hf : Continuous f) : UniformContinuous f :=
  CompactSpace.uniformContinuous_of_continuous hf

end Topology

