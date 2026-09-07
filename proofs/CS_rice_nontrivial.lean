/-
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede every command, including module doc-comments `/-! ... -/`,
-- so the header above is written as a plain block comment and repeated as a module docstring below.)

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

open Nat.Partrec

/-- **Rice's theorem.** Let `P` be a *semantic* property of programs (codes for partial
recursive functions): whether `P` holds of a code depends only on the partial function that
code computes. If `P` is *nontrivial*, i.e. some program satisfies it and some program does
not, then `P` is undecidable.

The proof is immediate from `ComputablePred.rice₂` in Mathlib. -/
theorem rice_nontrivial (P : Code → Prop)
    (hsem : ∀ c₁ c₂ : Code, Code.eval c₁ = Code.eval c₂ → (P c₁ ↔ P c₂))
    (cyes cno : Code) (hyes : P cyes) (hno : ¬ P cno) :
    ¬ ComputablePred P := by
  intro hcomp
  rcases (ComputablePred.rice₂ {c | P c} hsem).mp hcomp with h | h
  · have : cyes ∈ ({c | P c} : Set Code) := hyes
    rw [h] at this
    exact this
  · exact hno (by
      have : cno ∈ ({c | P c} : Set Code) := by rw [h]; trivial
      exact this)

end CS

