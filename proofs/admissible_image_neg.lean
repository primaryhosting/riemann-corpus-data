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

def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

def OmitsResidue (p : ℕ) (H : Finset ℤ) : Prop :=
  ∃ r : ZMod p, r ∉ residueImage p H

def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → OmitsResidue p H

/-- Negation acts as a bijection on residues mod every prime, so it preserves
admissibility. -/
theorem admissible_image_neg (S : Finset ℤ) (h : Admissible S) :
    Admissible (S.image (fun x => -x)) := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  refine ⟨-r, fun hmem => hr ?_⟩
  simp only [residueImage, Finset.mem_image, Finset.image_image, Function.comp] at hmem ⊢
  obtain ⟨x, hx, hxe⟩ := hmem
  exact ⟨x, hx, by push_cast at hxe ⊢; linear_combination -hxe⟩

