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
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry

If a group acts transitively on a finite nonempty set, then any invariant probability
weight on that set is the uniform distribution.
-/

open scoped BigOperators

namespace Brockian.EquidistributionUniformity

/-- An invariant weight on a set carrying a transitive symmetry group is constant. -/
theorem constant_of_transitive_symmetry
    {G X : Type*} [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x y : X, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Equidistribution from transitive symmetry.**  If a group `G` acts transitively on a
finite nonempty set `X`, then every `G`-invariant probability weight `w : X → ℝ` is the
uniform distribution: `w x = 1 / |X|` for every `x`. -/
theorem equidistribution_of_transitive_symmetry
    {G X : Type*} [Group G] [MulAction G X] [Fintype X] [Nonempty X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ x : X, w x = 1) :
    ∀ x : X, w x = 1 / (Fintype.card X : ℝ) := by
  intro x
  have hconst : ∀ y : X, w y = w x :=
    fun y => constant_of_transitive_symmetry htrans w hinv y x
  have hcard : (Fintype.card X : ℝ) * w x = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  field_simp
  linarith [hcard]

end Brockian.EquidistributionUniformity

