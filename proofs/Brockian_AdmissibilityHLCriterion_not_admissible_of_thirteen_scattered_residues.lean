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
  Target theorem `not_admissible_of_thirteen_scattered_residues` for the corpus module
  `Brockian.AdmissibilityHLCriterion`.

  The corpus modules themselves are not part of this project, so the corpus definitions
  the goal is phrased in terms of (`residueImage`, `OmitsResidue`, `Admissible`) are
  reproduced here verbatim, in their original namespace, purely so that the statement
  elaborates.  Nothing else from the corpus is restated or re-proved.
-/

open Finset

namespace Brockian.AdmissibilityHLCriterion

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

/-- **COMPUTATION.** The thirteen-element set `{0, 3, 8, 12, 14, 23, 30, 35, 37, 44, 45,
54, 59}` reduces mod `13` to the residues `0, 3, 8, 12, 1, 10, 4, 9, 11, 5, 6, 2, 7`,
i.e. to all of `ZMod 13`, so it omits no residue class mod `13` and is inadmissible. -/
theorem not_admissible_of_thirteen_scattered_residues :
    ¬ Admissible ({0, 3, 8, 12, 14, 23, 30, 35, 37, 44, 45, 54, 59} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 13 (by norm_num)
  exact hr (by revert r; decide)

end Brockian.AdmissibilityHLCriterion

