/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Math

variable {V W : Type*}

/-- The neighbourhood, inside the second vertex class `W`, of a finite set `A` of vertices of the
first vertex class `V`, in the bipartite graph whose adjacency relation is `adj`. -/
def hallNeighbors [Fintype W] (adj : V → W → Prop) [DecidableRel adj] (A : Finset V) : Finset W :=
  {w | ∃ v ∈ A, adj v w}

@[simp]
theorem mem_hallNeighbors [Fintype W] (adj : V → W → Prop) [DecidableRel adj] {A : Finset V}
    {w : W} : w ∈ hallNeighbors adj A ↔ ∃ v ∈ A, adj v w := by
  simp [hallNeighbors]

/-- **Hall's marriage theorem**, matching form: for a bipartite graph with vertex classes `V` and
`W` (`W` finite) and adjacency relation `adj`, there is a matching saturating `V` — that is, an
injective map `f : V → W` with every vertex `v` adjacent to `f v` — if and only if Hall's
condition holds: every finite set `A` of vertices of `V` has at least `#A` neighbours. -/
theorem halls_marriage_saturating [Fintype W] (adj : V → W → Prop) [DecidableRel adj] :
    (∃ f : V → W, Function.Injective f ∧ ∀ v : V, adj v (f v)) ↔
      ∀ A : Finset V, A.card ≤ (hallNeighbors adj A).card :=
  (Fintype.all_card_le_filter_rel_iff_exists_injective adj).symm

/-- **Hall's marriage theorem**: a bipartite graph with vertex classes `V` and `W` of the same
(finite) cardinality and adjacency relation `adj` has a perfect matching — a bijection
`f : V → W` with each vertex `v` adjacent to `f v` — if and only if Hall's condition holds:
for every set `A` of vertices of `V`, the set of neighbours of `A` has at least `#A` elements. -/
theorem halls_marriage [Fintype V] [Fintype W] (adj : V → W → Prop) [DecidableRel adj]
    (hcard : Fintype.card V = Fintype.card W) :
    (∃ f : V → W, Function.Bijective f ∧ ∀ v : V, adj v (f v)) ↔
      ∀ A : Finset V, A.card ≤ (hallNeighbors adj A).card := by
  rw [← halls_marriage_saturating adj]
  constructor
  · rintro ⟨f, hf, hadj⟩
    exact ⟨f, hf.injective, hadj⟩
  · rintro ⟨f, hf, hadj⟩
    exact ⟨f, (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩, hadj⟩

end Math

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

