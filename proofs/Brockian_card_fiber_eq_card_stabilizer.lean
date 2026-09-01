import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000

namespace Brockian
namespace EquidistributionUniformity

/-- **Fibres of a transitive action are cosets of a stabiliser.**

If a group `G` acts transitively on `X` and `g₀ • x = y`, then the set of group elements
carrying `x` to `y` is in bijection with the stabiliser of `x`; in particular the fibres of
the orbit map `g ↦ g • x` all have the same cardinality. -/
theorem card_fiber_eq_card_stabilizer
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    (x y : X) (g₀ : G) (hg₀ : g₀ • x = y) :
    {g : G | g • x = y}.toFinset.card = Fintype.card ↥(MulAction.stabilizer G x) := by
  have hset : {g : G | g • x = y}.toFinset
      = Finset.univ.filter (fun g : G => g • x = y) := by
    ext g; simp
  rw [hset, Fintype.card_subtype]
  refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun h _ => g₀ * h) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    simp [MulAction.mem_stabilizer_iff, mul_smul, ha, ← hg₀]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [mul_smul, MulAction.mem_stabilizer_iff.mp hb, hg₀]
  · intro a _; simp
  · intro b _; simp

/-- **Equidistribution of a transitive symmetry group.**

Let a finite group `G` act transitively on a finite set `X`. Then the orbit map
`g ↦ g • x` distributes the group uniformly over `X`: for every target point `y`, the number
of symmetries carrying `x` to `y` is exactly `|G| / |X|`, stated multiplicatively as

`#{g : G | g • x = y} * |X| = |G|`.

In particular the count is independent of `y`, i.e. the uniform distribution on `G`
pushes forward to the uniform distribution on `X`. -/
theorem equidistribution_of_transitive_symmetry
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [MulAction.IsPretransitive G X] (x y : X) :
    {g : G | g • x = y}.toFinset.card * Fintype.card X = Fintype.card G := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G x y
  have hstab := card_fiber_eq_card_stabilizer x y g₀ hg₀
  have horb : Fintype.card ↥(MulAction.orbit G x) = Fintype.card X :=
    Fintype.card_congr ((Equiv.setCongr (MulAction.orbit_eq_univ G x)).trans (Equiv.Set.univ X))
  rw [hstab, ← horb, mul_comm]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

/-- Consequence: the fibre counts of the orbit map are independent of the target point,
which is the equidistribution statement in its "all fibres have equal size" form. -/
theorem card_fiber_eq_card_fiber
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [MulAction.IsPretransitive G X] (x y y' : X) :
    {g : G | g • x = y}.toFinset.card = {g : G | g • x = y'}.toFinset.card := by
  have h1 := equidistribution_of_transitive_symmetry (G := G) x y
  have h2 := equidistribution_of_transitive_symmetry (G := G) x y'
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_right hX (h1.trans h2.symm)

end EquidistributionUniformity
end Brockian

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

