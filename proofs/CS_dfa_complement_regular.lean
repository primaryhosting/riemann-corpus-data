import Mathlib

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A language is *regular* if it is the language accepted by some
deterministic finite automaton (a `DFA` with finitely many states). -/
def IsRegular {α : Type*} (L : Language α) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), M.accepts = L

/-- The DFA obtained from `M` by complementing its set of accepting states. -/
def complDFA {α σ : Type*} (M : DFA α σ) : DFA α σ :=
  { step := M.step, start := M.start, accept := M.acceptᶜ }

@[simp]
theorem eval_complDFA {α σ : Type*} (M : DFA α σ) (x : List α) :
    (complDFA M).eval x = M.eval x := rfl

/-- The complement automaton accepts exactly the complement language. -/
theorem accepts_complDFA {α σ : Type*} (M : DFA α σ) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext x
  show (complDFA M).eval x ∈ (complDFA M).accept ↔ ¬ (M.eval x ∈ M.accept)
  rfl

/-- **Regular languages are closed under complement.** -/
theorem dfa_complement_regular {α : Type*} (L : Language α) (hL : IsRegular L) :
    IsRegular Lᶜ := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  exact ⟨σ, hσ, complDFA M, accepts_complDFA M⟩

end CS

