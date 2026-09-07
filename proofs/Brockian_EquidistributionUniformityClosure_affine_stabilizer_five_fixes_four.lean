/-
  Brockian/EquidistributionUniformityClosure.lean

  B1 closure / guardrail: the affine endpoint-stabilizer obstruction for q = 5.

  `EquidistributionUniformity` already proved that the endpoint reflection
  `a |-> -g - a` is not transitive on the q = 5, g = 2 admissible classes.  The
  prose there also identifies the stronger reason: any affine symmetry preserving
  the two forbidden endpoints `{0, -g}` is either the identity or that reflection.

  This file turns that stronger q = 5 statement into Lean.  It does not prove
  singular-series uniformity.  It proves the opposite boundary: affine endpoint
  symmetry cannot supply the missing q = 5 transitivity hypothesis, so any q = 5
  uniformity proof must use genuine singular-series arithmetic beyond these
  finite affine symmetries.
-/
import Brockian.EquidistributionUniformity

set_option autoImplicit false

open Finset
open Brockian.EquidistributionUniformity

namespace Brockian.EquidistributionUniformityClosure

/-- The q = 5, g = 2 forbidden endpoint set `{0, -g}`; since `-2 = 3` in
`ZMod 5`, this is `{0, 3}`. -/
def forbiddenFive : Finset (ZMod 5) := {0, 3}

/-- The affine map `x |-> u*x + c` on `ZMod 5`, with unit slope. -/
def affineMapFive (u : (ZMod 5)ˣ) (c x : ZMod 5) : ZMod 5 :=
  (u : ZMod 5) * x + c

/-- The image of the two forbidden endpoints under an affine map. -/
def forbiddenImageFive (u : (ZMod 5)ˣ) (c : ZMod 5) : Finset (ZMod 5) :=
  {affineMapFive u c 0, affineMapFive u c 3}

/-- An affine map setwise stabilizes the forbidden endpoint set `{0, -2}`. -/
def AffineStabilizesForbiddenFive (u : (ZMod 5)ˣ) (c : ZMod 5) : Prop :=
  forbiddenImageFive u c = forbiddenFive

/-- **Affine endpoint-stabilizer classification for q = 5, g = 2.**
An affine map `x |-> u*x+c` preserving the two forbidden endpoints `{0, -2}` is
either the identity or the endpoint reflection `x |-> -2-x`.

This is finite algebra only: the four possible unit slopes and five translations
are exhausted by kernel computation. -/
theorem affine_stabilizer_five_classification
    (u : (ZMod 5)ˣ) (c : ZMod 5)
    (hstab : AffineStabilizesForbiddenFive u c) :
    (∀ x : ZMod 5, affineMapFive u c x = x) ∨
      (∀ x : ZMod 5, affineMapFive u c x = reflect 5 (2 : ZMod 5) x) := by
  fin_cases u <;> fin_cases c <;>
    simp [AffineStabilizesForbiddenFive, forbiddenImageFive, forbiddenFive, affineMapFive] at hstab ⊢ <;>
    first
    | contradiction
    | left; intro x; fin_cases x <;> decide
    | right; intro x; fin_cases x <;> decide

/-- Every affine endpoint-stabilizer fixes the admissible class `4`. -/
theorem affine_stabilizer_five_fixes_four
    (u : (ZMod 5)ˣ) (c : ZMod 5)
    (hstab : AffineStabilizesForbiddenFive u c) :
    affineMapFive u c 4 = 4 := by
  rcases affine_stabilizer_five_classification u c hstab with hid | href
  · exact hid 4
  · rw [href, reflect_five_fixes_four]

/-- The cyclic orbit of `4` under any affine endpoint-stabilizer is the singleton
`{4}`. -/
theorem affine_stabilizer_five_four_orbit
    (u : (ZMod 5)ˣ) (c : ZMod 5)
    (hstab : AffineStabilizesForbiddenFive u c) (n : ℕ) :
    (affineMapFive u c)^[n] 4 = 4 :=
  Function.iterate_fixed (affine_stabilizer_five_fixes_four u c hstab) n

/-- **No affine endpoint-stabilizer is transitive on the q = 5, g = 2 admissible
classes.** Since every such affine map fixes `4`, no iterate can send the admissible
class `4` to the admissible class `1`.

This strengthens `reflection_not_transitive_five`: the obstruction is not merely
that the reflection is too small; the entire natural affine stabilizer of the
forbidden endpoint set is too small. -/
theorem affine_stabilizer_five_not_transitive
    (u : (ZMod 5)ˣ) (c : ZMod 5)
    (hstab : AffineStabilizesForbiddenFive u c) :
    ¬ IterTransitive (2 : ZMod 5) (affineMapFive u c) := by
  intro htrans
  obtain ⟨n, hn⟩ := htrans 4 (by decide) 1 (by decide)
  rw [affine_stabilizer_five_four_orbit u c hstab n] at hn
  exact absurd hn (by decide)

end Brockian.EquidistributionUniformityClosure
