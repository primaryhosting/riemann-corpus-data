/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **The halting problem is undecidable.**

There is no total computable function `H : ℕ → ℕ → Bool` which, given (a code for) a program
`p` and an input `x`, decides whether the program `p` halts on input `x`.

Here programs are the partial recursive programs `Nat.Partrec.Code`, encoded as natural numbers
via the (computable) denumeration `Denumerable.ofNat`, and "`p` halts on `x`" is
`(eval (Denumerable.ofNat Code p) x).Dom`, i.e. the partial function computed by `p` is defined at `x`.

The proof reduces to Mathlib's `ComputablePred.halting_problem`, which is proved by
diagonalization (via Rice's theorem / the recursion theorem). -/
theorem halting_undecidable :
    ¬ ∃ H : ℕ → ℕ → Bool,
        Computable₂ H ∧ ∀ p x : ℕ, H p x = true ↔ (eval (Denumerable.ofNat Code p) x).Dom := by
  rintro ⟨H, hHcomp, hH⟩
  -- Specialising the input to `0`, `H` would decide the halting problem for input `0`.
  refine ComputablePred.halting_problem 0 ?_
  have hiff : ∀ c : Code, (eval c 0).Dom ↔ H (Encodable.encode c) 0 = true := by
    intro c
    rw [hH (Encodable.encode c) 0, Denumerable.ofNat_encode]
  have hdec : DecidablePred fun c : Code => (eval c 0).Dom := fun c =>
    decidable_of_iff _ (hiff c).symm
  refine ⟨hdec, ?_⟩
  have hcomp : Computable fun c : Code => H (Encodable.encode c) 0 :=
    hHcomp.comp (Computable.encode.comp Computable.id) (Computable.const 0)
  refine hcomp.of_eq fun c => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact (hiff c).symm

end CS

