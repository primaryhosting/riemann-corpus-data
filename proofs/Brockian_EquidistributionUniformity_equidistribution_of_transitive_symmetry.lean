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

A weight function on a finite set which is invariant under a group acting
transitively on that set is necessarily constant; if moreover its total mass is
`1`, then it is the uniform distribution.

The main result `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry`
is stated unconditionally: the equidistribution conclusion is *derived* from the
transitivity and invariance hypotheses, rather than being assumed.
-/

namespace Brockian
namespace EquidistributionUniformity

open Finset

variable {X : Type*} {G : Type*}

/-- A function invariant under a transitive group action is constant. -/
theorem const_of_transitive_invariant [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] {M : Type*} (w : X → M)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x) (x y : X) :
    w x = w y := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  exact (hinv g x).symm

/-- **Equidistribution from transitive symmetry.**

If a group `G` acts transitively on a nonempty finite type `X` and `w : X → ℝ`
is a `G`-invariant weight of total mass `1`, then `w` is the uniform
distribution `x ↦ 1 / card X`. -/
theorem equidistribution_of_transitive_symmetry [Fintype X] [Nonempty X]
    [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (w : X → ℝ)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ x : X, w x = 1) (x : X) :
    w x = (Fintype.card X : ℝ)⁻¹ := by
  have hconst : ∀ y : X, w y = w x := fun y =>
    const_of_transitive_invariant (G := G) w hinv y x
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card X := Fintype.card_pos
    positivity
  have key : (Fintype.card X : ℝ) * w x = 1 := by
    calc (Fintype.card X : ℝ) * w x
        = ∑ _y : X, w x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ y : X, w y := Finset.sum_congr rfl fun y _ => (hconst y).symm
      _ = 1 := hsum
  field_simp
  linarith [key]

end EquidistributionUniformity
end Brockian

