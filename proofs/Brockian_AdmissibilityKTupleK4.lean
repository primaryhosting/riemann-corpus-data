/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- A finite set of integers is **admissible** (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if, for every prime `p`, its reduction modulo `p` misses
at least one residue class. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- A set of integers with fewer than `p` elements cannot cover all residues mod `p`. -/
theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro a _
    obtain ⟨h, hh, hha⟩ := hcon a
    exact Finset.mem_image.2 ⟨h, hh, hha⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at hle
  exact absurd (hle.trans Finset.card_image_le) (by omega)

/-- The `4`-tuple `(0, 2, 6, 8)` misses a residue class modulo `2`. -/
theorem missed_residue_two : ∃ a : ZMod 2, ∀ h ∈ ({0, 2, 6, 8} : Finset ℤ), (h : ZMod 2) ≠ a := by
  decide

/-- The `4`-tuple `(0, 2, 6, 8)` misses a residue class modulo `3`. -/
theorem missed_residue_three :
    ∃ a : ZMod 3, ∀ h ∈ ({0, 2, 6, 8} : Finset ℤ), (h : ZMod 3) ≠ a := by
  decide

/-- **Admissibility for `4`-tuples.** The `4`-element set `{0, 2, 6, 8}` is an admissible
`k`-tuple with `k = 4`: it has exactly four elements, and for every prime `p` some residue
class mod `p` is missed by it. -/
theorem AdmissibilityKTupleK4 :
    (({0, 2, 6, 8} : Finset ℤ).card = 4) ∧ Admissible ({0, 2, 6, 8} : Finset ℤ) := by
  refine ⟨by decide, ?_⟩
  intro p hp
  have hcard : (({0, 2, 6, 8} : Finset ℤ)).card = 4 := by decide
  by_cases hp2 : p = 2
  · subst hp2; exact missed_residue_two
  by_cases hp3 : p = 3
  · subst hp3; exact missed_residue_three
  -- otherwise `p ≥ 5 > 4 = card`, since `4` is not prime
  refine exists_missed_residue_of_card_lt _ p hp ?_
  rw [hcard]
  have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
  have := hp.two_le
  omega

end Brockian

