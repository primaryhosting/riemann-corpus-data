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

/-
# Cayley
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.cayley
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GroupTheory

/-- **Cayley's theorem**: every group `G` embeds into the symmetric group on its
underlying set, via an injective group homomorphism `G →* Equiv.Perm G`. -/
theorem cayley (G : Type*) [Group G] :
    ∃ f : G →* Equiv.Perm G, Function.Injective f := by
  refine ⟨MulAction.toPermHom G G, fun a b hab => ?_⟩
  have h := congrArg (fun e : Equiv.Perm G => e 1) hab
  simpa using h

end GroupTheory

