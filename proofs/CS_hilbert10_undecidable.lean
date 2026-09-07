/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

universe u

local infixr:65 " ⊗ " => Sum.elim

/-! ## Exponential polynomials

An *exponential polynomial* in variables of type `α` is built from variables and natural
number constants using addition, multiplication and exponentiation.  These are the objects
occurring in the Davis–Putnam–Robinson theorem. -/

/-- Syntax of exponential polynomials with variables in `α`. -/
inductive ExpPoly (α : Type u) : Type u
  | var : α → ExpPoly α
  | const : ℕ → ExpPoly α
  | add : ExpPoly α → ExpPoly α → ExpPoly α
  | mul : ExpPoly α → ExpPoly α → ExpPoly α
  | pow : ExpPoly α → ExpPoly α → ExpPoly α

/-- Evaluation of an exponential polynomial at a valuation `v : α → ℕ`. -/
def ExpPoly.eval {α : Type u} : ExpPoly α → (α → ℕ) → ℕ
  | .var i, v => v i
  | .const n, _ => n
  | .add p q, v => p.eval v + q.eval v
  | .mul p q, v => p.eval v * q.eval v
  | .pow p q, v => p.eval v ^ q.eval v

/-- A set `S ⊆ ℕ^α` is *exponential Diophantine* if it is the projection of the solution set
of an equation between two exponential polynomials. -/
def ExpDioph {α : Type u} (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type u) (e f : ExpPoly (α ⊕ β)), ∀ v, S v ↔ ∃ t, e.eval (v ⊗ t) = f.eval (v ⊗ t)

/-- Every exponential polynomial defines a Diophantine function.  This uses Matiyasevic's
theorem (`Dioph.pow_dioph`), i.e. that the graph of exponentiation is Diophantine. -/
theorem diophFn_expPoly_eval {α : Type} (p : ExpPoly α) :
    Dioph.DiophFn (fun v : α → ℕ => p.eval v) := by
  induction p with
  | var i => exact Dioph.proj_dioph i
  | const n => exact Dioph.const_dioph n
  | add p q hp hq => exact Dioph.add_dioph hp hq
  | mul p q hp hq => exact Dioph.mul_dioph hp hq
  | pow p q hp hq => exact Dioph.pow_dioph hp hq

/-- **Exponentiation can be eliminated**: every exponential Diophantine set is Diophantine.
This is the Diophantine-representation half of Matiyasevic's contribution to the MRDP
theorem, obtained here from `Dioph.pow_dioph`. -/
theorem dioph_of_expDioph {α : Type} {S : Set (α → ℕ)} (h : ExpDioph S) : Dioph S := by
  obtain ⟨β, e, f, hS⟩ := h
  have hEq : Dioph {w : α ⊕ β → ℕ | e.eval w = f.eval w} :=
    Dioph.eq_dioph (diophFn_expPoly_eval e) (diophFn_expPoly_eval f)
  exact Dioph.ext (Dioph.ex_dioph hEq) fun v => (hS v).symm

/-- Every integer polynomial is the difference of two exponential polynomials with values
in `ℕ`. -/
theorem exists_expPoly_sub {α : Type u} (p : Poly α) :
    ∃ e f : ExpPoly α, ∀ v, (p v : ℤ) = (e.eval v : ℤ) - (f.eval v : ℤ) := by
  induction p using Poly.induction with
  | H1 i => exact ⟨.var i, .const 0, fun v => by simp [ExpPoly.eval]⟩
  | H2 n => exact ⟨.const n.toNat, .const (-n).toNat, fun v => by simp [ExpPoly.eval]⟩
  | H3 p q hp hq =>
    obtain ⟨e₁, f₁, h₁⟩ := hp
    obtain ⟨e₂, f₂, h₂⟩ := hq
    refine ⟨.add e₁ f₂, .add f₁ e₂, fun v => ?_⟩
    simp only [Poly.sub_apply, ExpPoly.eval, h₁ v, h₂ v]
    push_cast
    ring
  | H4 p q hp hq =>
    obtain ⟨e₁, f₁, h₁⟩ := hp
    obtain ⟨e₂, f₂, h₂⟩ := hq
    refine ⟨.add (.mul e₁ e₂) (.mul f₁ f₂), .add (.mul e₁ f₂) (.mul f₁ e₂), fun v => ?_⟩
    simp only [Poly.mul_apply, ExpPoly.eval, h₁ v, h₂ v]
    push_cast
    ring

/-- Every Diophantine set is exponential Diophantine (exponentiation may simply be unused). -/
theorem expDioph_of_dioph {α : Type} {S : Set (α → ℕ)} (h : Dioph S) : ExpDioph S := by
  obtain ⟨β, p, hp⟩ := h
  obtain ⟨e, f, hef⟩ := exists_expPoly_sub p
  refine ⟨β, e, f, fun v => (hp v).trans ⟨?_, ?_⟩⟩ <;> rintro ⟨t, ht⟩ <;>
    exact ⟨t, by have := hef (v ⊗ t); omega⟩

/-- **Matiyasevic's theorem**: a set of tuples of naturals is Diophantine if and only if it is
exponential Diophantine. -/
theorem dioph_iff_expDioph {α : Type} {S : Set (α → ℕ)} : Dioph S ↔ ExpDioph S :=
  ⟨expDioph_of_dioph, dioph_of_expDioph⟩

/-! ## The Davis–Putnam–Robinson theorem, as a hypothesis

The remaining ingredient of the MRDP theorem is the Davis–Putnam–Robinson theorem: every
recursively enumerable set of naturals admits an exponential Diophantine representation.
This arithmetisation of computation is not available in Mathlib, so it is carried here as an
explicit hypothesis of the main theorem. -/

/-- The Davis–Putnam–Robinson theorem: every recursively enumerable predicate on `ℕ` is
exponential Diophantine (as a subset of `ℕ^Unit`). -/
def DavisPutnamRobinson : Prop :=
  ∀ A : ℕ → Prop, REPred A → ExpDioph {v : Unit → ℕ | A (v ())}

/-- The MRDP theorem: every recursively enumerable predicate on `ℕ` is Diophantine. -/
def MRDP : Prop :=
  ∀ A : ℕ → Prop, REPred A → Dioph {v : Unit → ℕ | A (v ())}

/-- By Matiyasevic's theorem, the MRDP theorem is equivalent to the Davis–Putnam–Robinson
theorem: eliminating exponentiation is the only gap between the two. -/
theorem mrdp_iff_davisPutnamRobinson : MRDP ↔ DavisPutnamRobinson :=
  ⟨fun h A hA => expDioph_of_dioph (h A hA), fun h A hA => dioph_of_expDioph (h A hA)⟩

/-- Consequence of the Davis-Putnam-Robinson theorem: every recursively enumerable predicate
on `ℕ` is Diophantine, i.e. of the form `fun a => ∃ t, p (a, t) = 0` for an integer
polynomial `p`.  This is the **MRDP theorem**. -/
theorem mrdp_of_dpr (hDPR : DavisPutnamRobinson) (A : ℕ → Prop) (hA : REPred A) :
    ∃ (β : Type) (p : Poly (Unit ⊕ β)),
      ∀ a : ℕ, A a ↔ ∃ t : β → ℕ, p ((fun _ => a) ⊗ t) = 0 := by
  obtain ⟨β, p, hp⟩ := dioph_of_expDioph (hDPR A hA)
  exact ⟨β, p, fun a => hp (fun _ => a)⟩

/-! ## Undecidability of Hilbert's tenth problem -/

/-- The halting problem, transported along the standard numbering of partial recursive
programs: `haltsAt n` says that the `n`-th program halts on input `0`. -/
def haltsAt (n : ℕ) : Prop :=
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0).Dom

theorem rePred_haltsAt : REPred haltsAt :=
  (Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)).dom_re

theorem not_computablePred_haltsAt : ¬ ComputablePred haltsAt := by
  intro h
  obtain ⟨f, hf, hEq⟩ := ComputablePred.computable_iff.1 h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.2
    ⟨fun c => f (Encodable.encode c), hf.comp Computable.encode, funext fun c => ?_⟩)
  have := congrFun hEq (Encodable.encode c)
  simpa [haltsAt, Denumerable.ofNat_encode] using this

/-- **Hilbert's tenth problem is undecidable** (the MRDP theorem, modulo the
Davis–Putnam–Robinson arithmetisation of recursively enumerable sets).

There is a single polynomial `p` with integer coefficients, in one distinguished parameter
`a` and finitely many further unknowns `t`, such that no algorithm decides, given `a`,
whether the Diophantine equation `p (a, t) = 0` has a solution `t` in the natural numbers.
In particular there is no algorithm solving Hilbert's tenth problem in general. -/
theorem hilbert10_undecidable (hDPR : DavisPutnamRobinson) :
    ∃ (β : Type) (p : Poly (Unit ⊕ β)),
      ¬ ComputablePred (fun a : ℕ => ∃ t : β → ℕ, p ((fun _ => a) ⊗ t) = 0) := by
  obtain ⟨β, p, hp⟩ := mrdp_of_dpr hDPR haltsAt rePred_haltsAt
  exact ⟨β, p, fun hcomp => not_computablePred_haltsAt (hcomp.of_eq fun a => (hp a).symm)⟩

end CS

