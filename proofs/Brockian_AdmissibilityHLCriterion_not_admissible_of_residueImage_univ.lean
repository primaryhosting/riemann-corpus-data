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

namespace Brockian.AdmissibilityHLCriterion

/-!
The corpus module `Brockian.AdmissibilityHLCriterion` is not part of this project, so the
definitions the goal is phrased in terms of (`residueImage`, `OmitsResidue`, `Admissible`)
are reproduced here verbatim, in their original namespace, purely so that the statement
elaborates.  Nothing else from the corpus is restated or re-proved.
-/

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `H` *omits a residue class* mod `p`: some residue mod `p` is not occupied by `H`. -/
def OmitsResidue (p : ℕ) (H : Finset ℤ) : Prop :=
  ∃ r : ZMod p, r ∉ residueImage p H

/-- **Admissibility (Hardy–Littlewood).** A finite integer tuple `H` is admissible iff
for every prime `p` it omits at least one residue class mod `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → OmitsResidue p H

/-- If at some prime `p` the reduction of `S` covers every residue class, then `S` is not
admissible.

(The `[NeZero p]` binder is present only so that the `Fintype (ZMod p)` instance behind
`Finset.univ` is available while the statement elaborates in this standalone file; it is
implied by `hp` and is not used by the proof.) -/
theorem not_admissible_of_residueImage_univ {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset ℤ}
    (h : residueImage p S = Finset.univ) : ¬ Admissible S := by
  intro hA
  obtain ⟨r, hr⟩ := hA p hp
  exact hr (by rw [h]; exact Finset.mem_univ r)

end Brockian.AdmissibilityHLCriterion

