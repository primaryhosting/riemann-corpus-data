/-
  Proof of `Brockian.AdmissibilityHLCriterion.not_admissible_of_residueImage_univ`.

  The corpus module `Brockian.AdmissibilityHLCriterion` is not part of this project, so
  the three corpus declarations the goal is phrased in terms of (`residueImage`,
  `OmitsResidue`, `Admissible`) are reproduced here verbatim, in their original
  namespace, purely so that the statement elaborates.  Nothing else is restated.

  Note on the ambient instance: `Finset.univ : Finset (ZMod p)` needs `Fintype (ZMod p)`,
  which Mathlib provides from `NeZero p`.  In this standalone file that instance is
  supplied by a section `variable [NeZero p]` (harmless, since `p` is prime); the proof
  body itself is exactly the requested one and uses nothing beyond `hp` and `h`.
-/
import Mathlib

set_option autoImplicit false

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

section

variable {p : ℕ} [NeZero p]

/-- If the reduction of `S` mod some prime `p` covers every residue class, then `S` omits
no class mod `p`, hence `S` is not admissible. -/
theorem not_admissible_of_residueImage_univ (hp : p.Prime) {S : Finset ℤ}
    (h : residueImage p S = Finset.univ) : ¬ Admissible S := by
  intro hA
  obtain ⟨r, hr⟩ := hA p hp
  exact hr (h ▸ Finset.mem_univ r)

end

end Brockian.AdmissibilityHLCriterion

