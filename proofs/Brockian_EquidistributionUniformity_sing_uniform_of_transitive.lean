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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- For a transitive action, the fiber `{g | g • x = y}` over any point `y` is in bijection
with the stabilizer of `x`: the map `g ↦ g₀⁻¹ * g` (where `g₀ • x = y`) is a bijection from the
fiber onto `stabilizer G x`. -/
def fiberEquivStabilizer (x y : X) (g₀ : G) (hg₀ : g₀ • x = y) :
    {g : G // g • x = y} ≃ stabilizer G x where
  toFun g := ⟨g₀⁻¹ * g.1, by
    simp only [mem_stabilizer_iff, mul_smul, g.2, ← hg₀, inv_smul_smul]⟩
  invFun h := ⟨g₀ * h.1, by
    have h' : h.1 • x = x := h.2
    rw [mul_smul, h', hg₀]⟩
  left_inv g := by simp
  right_inv h := by simp

/-- **Uniformity of singleton fibers for a transitive action.**

If a group `G` acts transitively on `X`, then for every pair of points `x y : X` the set of
group elements carrying `x` to `y` satisfies `#{g | g • x = y} * #X = #G`; in particular its
cardinality does not depend on `x` and `y`.

In probabilistic terms, pushing the uniform distribution on a finite group `G` forward along
`g ↦ g • x` gives the uniform distribution on `X`: every singleton `{y}` receives the same mass.

This is the orbit–stabilizer theorem
(`MulAction.index_stabilizer_of_transitive` together with `Subgroup.card_mul_index`)
combined with the coset description of the fibers. -/
theorem sing_uniform_of_transitive [IsPretransitive G X] (x y : X) :
    Nat.card {g : G // g • x = y} * Nat.card X = Nat.card G := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G x y
  have hcard : Nat.card {g : G // g • x = y} = Nat.card (stabilizer G x) :=
    Nat.card_congr (fiberEquivStabilizer x y g₀ hg₀)
  rw [hcard, ← index_stabilizer_of_transitive G x, Subgroup.card_mul_index]

/-- Consequence: for a transitive action on a finite nonempty set, the fibers over any two
points have the same cardinality. -/
theorem sing_card_eq_of_transitive [IsPretransitive G X] [Finite X] [Nonempty X]
    (x y x' y' : X) :
    Nat.card {g : G // g • x = y} = Nat.card {g : G // g • x' = y'} := by
  have hX : (0 : ℕ) < Nat.card X := Nat.card_pos
  have h₁ := sing_uniform_of_transitive (G := G) x y
  have h₂ := sing_uniform_of_transitive (G := G) x' y'
  exact Nat.eq_of_mul_eq_mul_right hX (h₁.trans h₂.symm)

end Brockian.EquidistributionUniformity

