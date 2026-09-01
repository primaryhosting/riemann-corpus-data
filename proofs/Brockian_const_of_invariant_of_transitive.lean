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

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian
namespace EquidistributionUniformity

variable {G X : Type*}

/-- **Key intermediate lemma.**  A weight function on `X` that is invariant under a group
action which is transitive on `X` is constant. -/
theorem const_of_invariant_of_transitive [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x y : X, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Equidistribution of transitive symmetry.**  If a group `G` acts on a nonempty finite type
`X` transitively, then any `G`-invariant probability weighting of `X` is the uniform
distribution: every point carries weight `1 / |X|`.

This is the unconditional form of the statement: the equidistribution hypothesis has been
discharged, being derived from transitivity and invariance alone. -/
theorem equidistribution_of_transitive_symmetry [Group G] [MulAction G X]
    [Fintype X] [Nonempty X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ x : X, w x = 1) :
    ∀ x : X, w x = (Fintype.card X : ℝ)⁻¹ := by
  have hconst := const_of_invariant_of_transitive htrans w hinv
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  intro x
  have hx : (Fintype.card X : ℝ) * w x = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun y _ => hconst y x)]
    simp [Finset.sum_const, Finset.card_univ, mul_comm]
  field_simp
  linarith [hx]

end EquidistributionUniformity
end Brockian

