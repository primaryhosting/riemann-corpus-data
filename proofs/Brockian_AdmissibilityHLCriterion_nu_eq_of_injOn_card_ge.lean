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
  Target theorem `nu_eq_of_injOn_card_ge` for the corpus module
  `Brockian.AdmissibilityHLCriterion`.

  The corpus modules themselves are not part of this project, so the two corpus
  definitions the goal is phrased in terms of (`residueImage` and `nu`) are
  reproduced here verbatim, in their original namespace, purely so that the
  statement elaborates.  Nothing else from the corpus is restated or re-proved.
-/

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- If the reduction map is injective on `S` and `S` has at least `p` elements, then
`S` meets every residue class mod `p`, i.e. `ν_p(S) = p`. -/
theorem nu_eq_of_injOn_card_ge (p : ℕ) [NeZero p] (S : Finset ℤ)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, ((x : ZMod p) = (y : ZMod p)) → x = y)
    (hcard : p ≤ S.card) :
    nu p S = p := by
  have hcardeq : nu p S = S.card :=
    Finset.card_image_of_injOn (fun x hx y hy hxy => hinj x hx y hy hxy)
  have hle : nu p S ≤ p := by
    have := Finset.card_le_univ (residueImage p S)
    simpa [nu, ZMod.card] using this
  omega

end Brockian.AdmissibilityHLCriterion

