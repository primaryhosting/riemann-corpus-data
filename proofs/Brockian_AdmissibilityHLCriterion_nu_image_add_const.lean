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
  Target theorem `nu_image_add_const` for the corpus module
  `Brockian.AdmissibilityHLCriterion`.

  The corpus modules themselves (`Brockian.Admissibility`, `Brockian.AdmissibilityKTuple`,
  `Brockian.AdmissibilityCriterionScaffold`) are not part of this project, so the two
  corpus definitions the goal is phrased in terms of (`residueImage` and `nu`) are
  reproduced here verbatim, in their original namespace, purely so that the statement
  elaborates.  Nothing else from the corpus is restated or re-proved.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- Translating a finite integer tuple by a constant `c` leaves the local count `ν_p`
unchanged: reduction mod `p` turns the translation into addition of `(c : ZMod p)`,
which is a bijection of `ZMod p`. -/
theorem nu_image_add_const (p : ℕ) (S : Finset ℤ) (c : ℤ) :
    nu p (S.image (fun x => x + c)) = nu p S := by
  unfold nu residueImage
  rw [Finset.image_image]
  have h : (S.image ((fun n : ℤ => (n : ZMod p)) ∘ (fun x => x + c)))
      = (S.image (fun n : ℤ => (n : ZMod p))).image (fun y => y + (c : ZMod p)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simp
  rw [h, Finset.card_image_of_injective _ (add_left_injective _)]

end Brockian.AdmissibilityHLCriterion

