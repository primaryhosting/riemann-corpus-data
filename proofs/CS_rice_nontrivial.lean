import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Rice's theorem** (nontrivial form): a set `C` of programs (codes for partial recursive
functions) which is *semantic* (membership depends only on the partial function computed) and
*nontrivial* (some program is in `C` and some program is not) is undecidable. -/
theorem rice_nontrivial (C : Set Code)
    (hsem : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (ha : ∃ a : Code, a ∈ C) (hb : ∃ b : Code, b ∉ C) :
    ¬ ComputablePred (fun c : Code => c ∈ C) := by
  rintro ⟨inst, hcomp⟩
  obtain ⟨a, haC⟩ := ha
  obtain ⟨b, hbC⟩ := hb
  have hf : Computable (fun c : Code => cond (decide (c ∈ C)) b a) :=
    Computable.cond hcomp (Computable.const b) (Computable.const a)
  obtain ⟨c, hc⟩ := fixed_point hf
  have key : (cond (decide (c ∈ C)) b a) ∈ C ↔ c ∈ C := hsem _ _ hc
  by_cases H : c ∈ C
  · rw [decide_eq_true H, cond_true] at key
    exact hbC (key.2 H)
  · rw [decide_eq_false H, cond_false] at key
    exact H (key.1 haC)

end CS

