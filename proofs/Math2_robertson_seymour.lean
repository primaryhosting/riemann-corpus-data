/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
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

namespace Math2

/-- `IsMinor G H` states that `G` is a *minor* of `H`, expressed by the standard
"minor model" (branch set) definition: there is a family of pairwise disjoint, nonempty,
connected vertex sets `B v ⊆ W` (one for each vertex `v` of `G`) such that whenever
`u` and `v` are adjacent in `G` there is an edge of `H` between `B u` and `B v`. -/
def IsMinor {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ B : V → Set W,
    (∀ v, (B v).Nonempty) ∧
    (∀ u v, u ≠ v → Disjoint (B u) (B v)) ∧
    (∀ v, (H.induce (B v)).Connected) ∧
    (∀ u v, G.Adj u v → ∃ x ∈ B u, ∃ y ∈ B v, H.Adj x y)

/-- A finite graph, represented (up to isomorphism, without loss of generality) as a simple
graph on the vertex set `Fin n`. -/
abbrev FinGraph : Type := Σ n : ℕ, SimpleGraph (Fin n)

/-- The minor relation on finite graphs. -/
def MinorLE (G H : FinGraph) : Prop := IsMinor G.2 H.2

end Math2

