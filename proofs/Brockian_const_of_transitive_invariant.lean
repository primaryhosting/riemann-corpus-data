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
# Equidistribution from transitive symmetry

If a group `G` acts transitively on a finite nonempty type `X`, then every `G`-invariant
weighting of `X` whose total mass is `1` is the uniform weighting `x ↦ 1 / |X|`.

This is the "equidistribution uniformity" principle: transitive symmetry forces uniformity.

The main statement `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry`
is unconditional: the uniformity conclusion is derived, not assumed.
-/

namespace Brockian
namespace EquidistributionUniformity

open Finset

variable {G X : Type*} [Group G] [MulAction G X]

/-- An invariant weight function is constant along orbits; under a transitive action it is
therefore globally constant. -/
theorem const_of_transitive_invariant {M : Type*} (w : X → M)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x y : X, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Equidistribution from transitive symmetry.**

Let a group `G` act transitively on a finite nonempty type `X`, and let `w : X → ℝ` be a
`G`-invariant weight with total mass `1`. Then `w` is the uniform weight `x ↦ 1 / |X|`.

The uniformity of `w` is *concluded*, not hypothesized. -/
theorem equidistribution_of_transitive_symmetry [Fintype X] [Nonempty X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hsum : ∑ x : X, w x = 1)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x : X, w x = (Fintype.card X : ℝ)⁻¹ := by
  have hconst : ∀ x y : X, w x = w y := const_of_transitive_invariant w htrans hinv
  intro x
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty X›
  have hs : ∑ y : X, w y = (Fintype.card X : ℝ) * w x := by
    rw [Finset.sum_congr rfl (fun y _ => hconst y x)]
    simp [Finset.card_univ, mul_comm]
  rw [hs] at hsum
  field_simp
  linarith [hsum]

/-- Measure-theoretic form: a `G`-invariant probability mass function on a finite type with a
transitive `G`-action is the uniform distribution. -/
theorem pmf_eq_uniform_of_transitive_symmetry [Fintype X] [Nonempty X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (p : PMF X) (hinv : ∀ (g : G) (x : X), p (g • x) = p x) :
    p = PMF.uniformOfFintype X := by
  have hsum : ∑ x : X, (p x).toReal = 1 := by
    have h := p.tsum_coe
    have hfin : ∑' x : X, p x = ∑ x : X, p x := tsum_fintype _
    rw [hfin] at h
    have h2 : ((∑ x : X, p x : ENNReal)).toReal = (1 : ENNReal).toReal := by rw [h]
    rw [ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top p x)] at h2
    simpa using h2
  have hinvR : ∀ (g : G) (x : X), (p (g • x)).toReal = (p x).toReal := by
    intro g x; rw [hinv]
  have key := equidistribution_of_transitive_symmetry htrans (fun x => (p x).toReal) hsum hinvR
  ext x
  have hx : (p x).toReal = (Fintype.card X : ℝ)⁻¹ := key x
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty X›
  have hval : p x = ENNReal.ofReal ((Fintype.card X : ℝ)⁻¹) := by
    rw [← hx, ENNReal.ofReal_toReal (PMF.apply_ne_top p x)]
  rw [hval, PMF.uniformOfFintype_apply]
  rw [← ENNReal.ofReal_natCast (Fintype.card X), ← ENNReal.ofReal_inv_of_pos hcard]

end EquidistributionUniformity
end Brockian

