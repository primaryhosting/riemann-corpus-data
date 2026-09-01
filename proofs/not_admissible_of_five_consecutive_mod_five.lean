import Mathlib

def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

def OmitsResidue (p : ℕ) (H : Finset ℤ) : Prop :=
  ∃ r : ZMod p, r ∉ residueImage p H

def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → OmitsResidue p H

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

theorem not_admissible_of_five_consecutive_mod_five :
    ¬ Admissible ({0, 1, 2, 3, 4} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 5 (by norm_num)
  revert hr
  revert r
  decide

