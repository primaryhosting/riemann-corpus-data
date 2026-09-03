/-
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
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

namespace Math

open SimpleGraph

/-- **Hall's marriage theorem** for bipartite graphs, as an equivalence.

For a locally finite graph `G` bipartite with parts `p₁` and `p₂`, `G` has a perfect matching
if and only if Hall's condition holds: every set of vertices `s` has at least as many
neighbours (counted in the union of the neighbourhoods) as it has elements.

The right-to-left implication is the substantive direction (it needs bipartiteness); the
left-to-right implication holds for any locally finite graph. -/
theorem halls_marriage {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {p₁ p₂ : Set V}
    (hbip : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  constructor
  · rintro ⟨M, hM⟩ s
    rcases s.finite_or_infinite with hs | hs
    · have hfin : (⋃ x ∈ s, G.neighborSet x).Finite := hs.biUnion fun x _ => Set.toFinite _
      -- `f v` is the partner of `v` in the perfect matching `M`
      set f : V → V := fun v => (hM.1 (hM.2 v)).choose with hf
      have hadj : ∀ v, M.Adj v (f v) := fun v => (hM.1 (hM.2 v)).choose_spec.1
      refine Set.ncard_le_ncard_of_injOn f (fun a ha => ?_) (fun a _ b _ hab => ?_) hfin
      · exact Set.mem_biUnion ha (M.adj_sub (hadj a))
      · have h1 : M.Adj (f a) a := (hadj a).symm
        have h2 : M.Adj (f a) b := hab ▸ (hadj b).symm
        exact (hM.1 (hM.2 (f a))).unique h1 h2
    · simp [hs.ncard]
  · exact fun h => exists_isPerfectMatching_of_forall_ncard_le hbip h

end Math

