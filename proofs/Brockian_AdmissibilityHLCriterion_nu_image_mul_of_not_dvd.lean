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

open Finset

/-
  Target theorem `nu_image_mul_of_not_dvd` for the corpus module
  `Brockian.AdmissibilityHLCriterion`.

  The corpus module itself is not part of this project, so the two corpus definitions the
  goal is phrased in terms of (`residueImage` and `nu`) are reproduced here verbatim, in
  their original namespace, purely so that the statement elaborates.  Nothing else from
  the corpus is restated or re-proved.
-/

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- Dilating a finite integer tuple by an integer `a` that is not divisible by the prime
`p` leaves the local count `ν_p` unchanged: reduction mod `p` turns the dilation into
multiplication by the nonzero element `(a : ZMod p)` of the field `ZMod p`, which is a
bijection of `ZMod p`. -/
theorem nu_image_mul_of_not_dvd {p : ℕ} (hp : p.Prime) (a : ℤ)
    (ha : ¬ ((p : ℤ) ∣ a)) (S : Finset ℤ) :
    nu p (S.image (fun x => a * x)) = nu p S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha0 : (a : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold nu residueImage
  rw [Finset.image_image]
  have h : (S.image ((fun n : ℤ => (n : ZMod p)) ∘ (fun x => a * x)))
      = (S.image (fun n : ℤ => (n : ZMod p))).image (fun y => (a : ZMod p) * y) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simp
  rw [h, Finset.card_image_of_injective _ (mul_right_injective₀ ha0)]

end Brockian.AdmissibilityHLCriterion

