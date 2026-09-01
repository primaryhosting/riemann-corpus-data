import Mathlib

set_option autoImplicit false

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`.
(Reproduced from the corpus module so the statement elaborates.) -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- Monotonicity of the local count `ν_p` under inclusion. -/
theorem nu_mono {p : ℕ} {S T : Finset ℤ} (h : S ⊆ T) :
    nu p S ≤ nu p T :=
  Finset.card_le_card (Finset.image_subset_image h)

end Brockian.AdmissibilityHLCriterion

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

