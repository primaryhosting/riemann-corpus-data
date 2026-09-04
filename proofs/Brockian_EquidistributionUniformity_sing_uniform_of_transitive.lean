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

/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace EquidistributionUniformity

/-- A weight function on `X` that is invariant under a transitive action is constant. -/
theorem const_of_transitive {G X : Type*} [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (w : X → ℝ)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x y : X, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Uniformity of invariant distributions on singletons.**
If a group `G` acts transitively on a finite nonempty type `X` and `w : X → ℝ` is a
`G`-invariant weight function with total mass `1`, then `w` assigns to every singleton
the uniform value `1 / |X|`. -/
theorem sing_uniform_of_transitive {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] [Nonempty X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (w : X → ℝ)
    (hsum : ∑ x : X, w x = 1) (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x : X, w x = 1 / (Fintype.card X : ℝ) := by
  intro x
  have hconst : ∀ y : X, w y = w x := fun y => const_of_transitive htrans w hinv y x
  have hcard : (Fintype.card X : ℝ) * w x = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun y _ => hconst y)]
    simp [Finset.sum_const, Finset.card_univ, mul_comm]
  have hpos : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  field_simp at hcard ⊢
  linarith [hcard]

end EquidistributionUniformity
end Brockian

