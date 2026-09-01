/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Rice's theorem.**  Let `C` be any set of partial functions `ℕ →. ℕ` (a *semantic*
property of programs: membership depends only on the computed function, not on the code).
If the induced index set `{c | eval c ∈ C}` is nontrivial — some code computes a function
in `C` and some code computes a function not in `C` — then that index set is not recursive,
i.e. the predicate `fun c => eval c ∈ C` is not computable.

The proof is the standard one via Rogers' fixed point theorem: if the predicate were
decidable, the computable map sending a code `c` to a fixed code `b ∉ C` when `eval c ∈ C`
and to a fixed code `a ∈ C` otherwise would have a fixed point `c` with
`eval (f c) = eval c`, which is contradictory in both cases. -/
theorem rice_extended (C : Set (ℕ →. ℕ))
    (h₁ : ∃ a : Code, eval a ∈ C) (h₂ : ∃ b : Code, eval b ∉ C) :
    ¬ ComputablePred (fun c : Code => eval c ∈ C) := by
  rintro ⟨inst, hcomp⟩
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have hf : Computable (fun c : Code => bif (decide (eval c ∈ C)) then b else a) :=
    Computable.cond hcomp (Computable.const b) (Computable.const a)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point hf
  by_cases h : eval c ∈ C
  · simp only [h, decide_true, cond_true] at hc
    exact hb (hc ▸ h)
  · simp only [h, decide_false, cond_false] at hc
    exact h (hc ▸ ha)

end CS

#print axioms CS.rice_extended

