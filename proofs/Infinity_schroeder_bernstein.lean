/-
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Infinity

/-- **Cantor–Schröder–Bernstein**: if there are injections `X → Y` and `Y → X`,
then there is a bijection between `X` and `Y`. -/
theorem schroeder_bernstein {X Y : Type*} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Nonempty (X ≃ Y) := by
  obtain ⟨h, hh⟩ := Function.Embedding.schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h hh⟩

end Infinity

