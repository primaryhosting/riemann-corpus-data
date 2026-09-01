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
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Archive.Wiedijk100Theorems.FriendshipGraphs

namespace Frontier

/-- **The friendship theorem** (Erdős–Rényi–Sós): in a finite nonempty graph in which every
two distinct vertices have exactly one common neighbour, there is a vertex adjacent to all
other vertices.

The proof is obtained from Mathlib's `Theorems100.Friendship.friendship_theorem`
(`Archive/Wiedijk100Theorems/FriendshipGraphs.lean`), after translating the hypothesis
phrased with `Nat.card` into the `Fintype.card` form used there. -/
theorem friendship_theorem {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : ∀ v w : V, v ≠ w → Nat.card (G.commonNeighbors v w) = 1) :
    ∃ p : V, ∀ w : V, w ≠ p → G.Adj p w := by
  have hF : Theorems100.Friendship G := by
    intro v w hvw
    rw [Fintype.card_eq_nat_card]
    exact hG v w hvw
  obtain ⟨p, hp⟩ := Theorems100.friendship_theorem hF
  exact ⟨p, fun w hw => hp w (Ne.symm hw)⟩

end Frontier

