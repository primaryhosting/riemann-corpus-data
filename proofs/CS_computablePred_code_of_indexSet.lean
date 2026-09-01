/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The index set of a semantic property `P` of partial functions: the set of natural
numbers `n` such that the partial recursive function computed by the `n`-th code
satisfies `P`. -/
def indexSet (P : (ℕ →. ℕ) → Prop) : Set ℕ :=
  {n : ℕ | P (eval (Denumerable.ofNat Code n))}

/-- If the index set of a semantic property is decidable, then so is the property viewed
as a property of codes. -/
theorem computablePred_code_of_indexSet {P : (ℕ →. ℕ) → Prop}
    (h : ComputablePred fun n : ℕ => n ∈ indexSet P) :
    ComputablePred fun c : Code => P (eval c) := by
  obtain ⟨inst, hcomp⟩ := h
  have key : ∀ c : Code, (Encodable.encode c ∈ indexSet P) ↔ P (eval c) := by
    intro c
    simp only [indexSet, Set.mem_setOf_eq, Denumerable.ofNat_encode]
  refine ⟨fun c => decidable_of_iff _ (key c), ?_⟩
  have hc := hcomp.comp (Computable.encode (α := Code))
  refine hc.of_eq fun c => ?_
  simp only [decide_eq_decide]
  exact key c

/-- **Core of Rice's theorem, on codes.** If the property `P` of partial functions is decidable
from a code, then `P` cannot separate two partial recursive functions: it holds of every
partial recursive function as soon as it holds of one. This is proved directly from Kleene's
second recursion theorem (`Nat.Partrec.Code.fixed_point₂`): given a decision procedure for `P`,
build a program that, on a code `c` for itself, computes `g` if `P (eval c)` holds and `f`
otherwise; a fixed point of this construction contradicts the decision procedure unless `P g`
holds. -/
theorem rice_codes {P : (ℕ →. ℕ) → Prop} (h : ComputablePred fun c : Code => P (eval c))
    {f g : ℕ →. ℕ} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfP : P f) : P g := by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp Computable.fst)
        ((Partrec.nat_iff.2 hg).comp Computable.snd).to₂
        ((Partrec.nat_iff.2 hf).comp Computable.snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : P (eval c)
  · simp only [H, if_true] at e
    show P fun b => g b
    rwa [← e]
  · simp only [H, if_false] at e
    rw [e] at H
    exact absurd hfP H

/-- **Rice's theorem (extended form).** If `P` is a property of partial functions which is
nontrivial on the partial recursive functions — i.e. some partial recursive function `f`
satisfies `P` and some partial recursive function `g` does not — then the index set of `P`
is not recursive (not decidable). -/
theorem rice_extended (P : (ℕ →. ℕ) → Prop) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfP : P f) (hgP : ¬ P g) :
    ¬ ComputablePred fun n : ℕ => n ∈ indexSet P := by
  intro h
  exact hgP (rice_codes (computablePred_code_of_indexSet h) hf hg hfP)

/-- Every code evaluates to a partial recursive function. -/
theorem partrec_eval (c : Code) : Nat.Partrec (eval c) :=
  Partrec.nat_iff.1 (eval_part.comp (Computable.const c) Computable.id)

/-- **Rice's theorem, dichotomy form.** The index set of a property `P` of partial functions
is recursive if and only if `P` is trivial on the partial recursive functions, i.e. it holds
of all of them or of none of them. -/
theorem rice_extended_iff (P : (ℕ →. ℕ) → Prop) :
    (ComputablePred fun n : ℕ => n ∈ indexSet P) ↔
      ((∀ f : ℕ →. ℕ, Nat.Partrec f → P f) ∨ (∀ f : ℕ →. ℕ, Nat.Partrec f → ¬ P f)) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨g, hg, hgP⟩ := h1
    obtain ⟨f, hf, hfP⟩ := h2
    exact rice_extended P hf hg hfP hgP h
  · rintro (h | h)
    · have hall : ∀ n : ℕ, n ∈ indexSet P := fun n => h _ (partrec_eval _)
      exact ⟨fun n => Decidable.isTrue (hall n),
        (Computable.const true).of_eq fun n => by simp [hall n]⟩
    · have hnone : ∀ n : ℕ, n ∉ indexSet P := fun n => h _ (partrec_eval _)
      exact ⟨fun n => Decidable.isFalse (hnone n),
        (Computable.const false).of_eq fun n => by simp [hnone n]⟩

/-- An application, witnessing that the hypotheses of `rice_extended` are satisfiable: for each
input `n`, the set of indices of programs that halt on `n` is not recursive. -/
theorem indexSet_halting_not_computable (n : ℕ) :
    ¬ ComputablePred fun m : ℕ => m ∈ indexSet fun u : ℕ →. ℕ => (u n).Dom :=
  rice_extended _ Nat.Partrec.zero Nat.Partrec.none trivial not_false

end CS

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

