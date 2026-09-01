import Mathlib
import Archive.Sensitivity

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

namespace Frontier

/-- Two vertices of the `n`-dimensional Boolean hypercube `Fin n → Bool` are adjacent
when they differ in exactly one coordinate. -/
def HypercubeAdjacent {n : ℕ} (p q : Fin n → Bool) : Prop := ∃! i : Fin n, p i ≠ q i

/-- **Huang's sensitivity theorem** (Huang, 2019), in its degree ("combinatorial") form:
in the hypercube of dimension `n + 1`, any set `H` of strictly more than half of the
`2 ^ (n + 1)` vertices contains a vertex `q` having at least `√(n + 1)` neighbours inside `H`.

This is the key combinatorial ingredient from which the polynomial relation between the
sensitivity and the degree (equivalently, the block sensitivity) of a Boolean function follows.

The proof is obtained from the formalization of Knuth's account of Huang's spectral argument
available in the `Archive.Sensitivity` file of Mathlib
(`Sensitivity.huang_degree_theorem`). -/
theorem huang_sensitivity (n : ℕ) (H : Set (Fin (n + 1) → Bool)) (hH : 2 ^ n < H.ncard) :
    ∃ q ∈ H, Real.sqrt (n + 1) ≤ ({p ∈ H | HypercubeAdjacent q p}.ncard : ℝ) := by
  have hcard : (Set.toFinset (H : Set (Sensitivity.Q (n + 1)))).card ≥ 2 ^ n + 1 := by
    have : H.ncard = (Set.toFinset H).card := by
      rw [Set.ncard_eq_toFinset_card']
    omega
  obtain ⟨q, hqH, hq⟩ := Sensitivity.huang_degree_theorem (m := n) H hcard
  refine ⟨q, hqH, ?_⟩
  have hset : {p ∈ H | HypercubeAdjacent q p} = H ∩ q.adjacent := by
    ext p
    simp only [Sensitivity.Q.adjacent, HypercubeAdjacent, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  have hc : ({p ∈ H | HypercubeAdjacent q p}.ncard : ℝ)
      = ((Set.toFinset (H ∩ q.adjacent)).card : ℝ) := by
    rw [hset]
    norm_cast
    rw [Set.ncard_eq_toFinset_card']
  rw [hc]
  exact hq

end Frontier

#print axioms Frontier.huang_sensitivity

