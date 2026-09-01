import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the
theorem is satisfiable and the theorem is not vacuous.  We also record that the notion of
arithmetical definability used there is non-trivial (some relations *are* definable).
-/

namespace Frontier

/-- A Gödel numbering of arithmetical terms, using Cantor pairing. -/
def ATerm.enc : ATerm → Nat
  | .var i => Nat.pair 0 i
  | .zero => Nat.pair 1 0
  | .one => Nat.pair 2 0
  | .add t u => Nat.pair 3 (Nat.pair t.enc u.enc)
  | .mul t u => Nat.pair 4 (Nat.pair t.enc u.enc)

theorem ATerm.enc_injective : Function.Injective ATerm.enc := by
  intro t
  induction t with
  | var i =>
    intro u h
    cases u <;> simp [ATerm.enc, Nat.pair_eq_pair] at h ⊢
    omega
  | zero =>
    intro u h
    cases u <;> simp [ATerm.enc, Nat.pair_eq_pair] at h ⊢
  | one =>
    intro u h
    cases u <;> simp [ATerm.enc, Nat.pair_eq_pair] at h ⊢
  | add t₁ t₂ ih₁ ih₂ =>
    intro u h
    cases u <;> simp [ATerm.enc, Nat.pair_eq_pair] at h ⊢
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | mul t₁ t₂ ih₁ ih₂ =>
    intro u h
    cases u <;> simp [ATerm.enc, Nat.pair_eq_pair] at h ⊢
    exact ⟨ih₁ h.1, ih₂ h.2⟩

/-- A Gödel numbering of arithmetical formulas, using Cantor pairing. -/
def AForm.enc : AForm → Nat
  | .eq t u => Nat.pair 0 (Nat.pair t.enc u.enc)
  | .not p => Nat.pair 1 p.enc
  | .and p q => Nat.pair 2 (Nat.pair p.enc q.enc)
  | .ex i p => Nat.pair 3 (Nat.pair i p.enc)

theorem AForm.enc_injective : Function.Injective AForm.enc := by
  intro p
  induction p with
  | eq t u =>
    intro q h
    cases q <;> simp [AForm.enc, Nat.pair_eq_pair] at h ⊢
    exact ⟨ATerm.enc_injective h.1, ATerm.enc_injective h.2⟩
  | not p ih =>
    intro q h
    cases q <;> simp [AForm.enc, Nat.pair_eq_pair] at h ⊢
    exact ih h
  | and p₁ p₂ ih₁ ih₂ =>
    intro q h
    cases q <;> simp [AForm.enc, Nat.pair_eq_pair] at h ⊢
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | ex i p ih =>
    intro q h
    cases q <;> simp [AForm.enc, Nat.pair_eq_pair] at h ⊢
    exact ⟨h.1, ih h.2⟩

/-- The hypothesis of Tarski's theorem is satisfiable: injective Gödel numberings exist. -/
theorem exists_injective_code : ∃ code : AForm → Nat, Function.Injective code :=
  ⟨AForm.enc, AForm.enc_injective⟩

/-- Tarski's undefinability theorem for the concrete Gödel numbering `AForm.enc`. -/
theorem Tarski_undefinability_enc :
    ¬ ArithDefinableRel (ArithTruth AForm.enc) :=
  Tarski_undefinability AForm.enc AForm.enc_injective

/-- Arithmetical definability is not a vacuous notion: equality is definable. -/
theorem arithDefinableRel_eq : ArithDefinableRel (fun a b => a = b) :=
  ⟨.eq (.var 0) (.var 1), fun _ => Iff.rfl⟩

/-- Another sanity check: the divisibility relation is arithmetically definable. -/
theorem arithDefinableRel_dvd : ArithDefinableRel (fun a b => ∃ k, b = a * k) := by
  refine ⟨.ex 2 (.eq (.var 1) (.mul (.var 0) (.var 2))), fun v => ?_⟩
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by simpa [ATerm.eval, upd] using hk⟩
  · intro h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by simpa [ATerm.eval, upd] using hk⟩

end Frontier

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-! ## Syntax of first-order arithmetic

We work with the language of arithmetic `{0, 1, +, *, =}` interpreted in the standard model
`Nat`.  Variables are indexed by natural numbers, and an assignment is a function
`Nat → Nat`.

The development is deliberately self-contained, so that every notion occurring in the
statement of the theorem — syntax, satisfaction, definability, arithmetical truth — is
defined here explicitly.
-/

/-- Terms of the language of arithmetic. -/
inductive ATerm : Type
  | var : Nat → ATerm
  | zero : ATerm
  | one : ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm

/-- Value of a term in the standard model `Nat` under an assignment `v`. -/
def ATerm.eval (v : Nat → Nat) : ATerm → Nat
  | .var i => v i
  | .zero => 0
  | .one => 1
  | .add t u => t.eval v + u.eval v
  | .mul t u => t.eval v * u.eval v

/-- Formulas of the language of arithmetic.  The connectives `¬`, `∧` and the existential
quantifier suffice: the other connectives and `∀` are definable from them. -/
inductive AForm : Type
  | eq : ATerm → ATerm → AForm
  | not : AForm → AForm
  | and : AForm → AForm → AForm
  | ex : Nat → AForm → AForm

/-- Update an assignment at one variable. -/
def upd (v : Nat → Nat) (i m : Nat) : Nat → Nat := fun j => if j = i then m else v j

/-- Tarskian satisfaction in the standard model `Nat`: `φ.Sat v` says that the assignment
`v : Nat → Nat` satisfies the formula `φ` in the structure `(Nat, 0, 1, +, *, =)`. -/
def AForm.Sat : AForm → (Nat → Nat) → Prop
  | .eq t u, v => t.eval v = u.eval v
  | .not p, v => ¬ p.Sat v
  | .and p q, v => p.Sat v ∧ q.Sat v
  | .ex i p, v => ∃ m : Nat, p.Sat (upd v i m)

/-! ## Arithmetical definability -/

/-- A set `S ⊆ Nat` is *arithmetically definable* if some arithmetical formula `φ` is
satisfied exactly by those assignments whose value at the variable `x₀` lies in `S`.
Quantifying over all assignments simultaneously forces `φ` to have no free variable other
than `x₀`. -/
def ArithDefinable (S : Nat → Prop) : Prop :=
  ∃ φ : AForm, ∀ v : Nat → Nat, (φ.Sat v ↔ S (v 0))

/-- A binary relation on `Nat` is *arithmetically definable* if some arithmetical formula `φ`
is satisfied exactly by those assignments whose values at `x₀` and `x₁` are related.  Again,
quantifying over all assignments forces `φ` to have no free variables besides `x₀, x₁`. -/
def ArithDefinableRel (R : Nat → Nat → Prop) : Prop :=
  ∃ φ : AForm, ∀ v : Nat → Nat, (φ.Sat v ↔ R (v 0) (v 1))

/-- *Arithmetical truth* relative to a Gödel numbering `code` of arithmetical formulas:
`ArithTruth code m n` holds iff `m` is the Gödel number of an arithmetical formula that is
true in the standard model when its variables are given the value `n`.  This is the
satisfaction relation of `(Nat, 0, 1, +, *, =)`, transported along the numbering. -/
def ArithTruth (code : AForm → Nat) (m n : Nat) : Prop :=
  ∃ φ : AForm, code φ = m ∧ φ.Sat (fun _ => n)

/-! ## Tarski's undefinability theorem

The argument is Tarski's diagonal argument.  Given a putative truth formula one forms the
formula `¬ T(x₀, x₀)` and evaluates it at its own Gödel number.
-/

/-- Substituting `x₀` for `x₁` semantically, without any syntactic substitution:
`∃ x₁, (x₀ = x₁ ∧ T)` expresses `T(x₀, x₀)`. -/
private def selfApply (T : AForm) : AForm :=
  .ex 1 (.and (.eq (.var 0) (.var 1)) T)

private theorem selfApply_sat (T : AForm) (v : Nat → Nat) :
    (selfApply T).Sat v ↔ T.Sat (upd v 1 (v 0)) := by
  constructor
  · intro hex
    have hex' : ∃ m : Nat, (AForm.and (.eq (.var 0) (.var 1)) T).Sat (upd v 1 m) := hex
    match hex' with
    | ⟨m, hm, hT⟩ =>
      have hvm : v 0 = m := by
        have h0 : ATerm.eval (upd v 1 m) (.var 0) = ATerm.eval (upd v 1 m) (.var 1) := hm
        simpa [ATerm.eval, upd] using h0
      exact hvm ▸ hT
  · intro hT
    refine ⟨v 0, ?_, hT⟩
    show ATerm.eval (upd v 1 (v 0)) (.var 0) = ATerm.eval (upd v 1 (v 0)) (.var 1)
    simp [ATerm.eval, upd]

/-- **Tarski's undefinability theorem, diagonal form.**  For any injective Gödel numbering
`code`, the *diagonal* of arithmetical truth, i.e. the set of Gödel numbers `n` of
arithmetical formulas that are true of `n` itself, is not arithmetically definable. -/
theorem diagonal_truth_not_ArithDefinable (code : AForm → Nat)
    (hcode : Function.Injective code) :
    ¬ ArithDefinable (fun n => ArithTruth code n n) := by
  intro hdef
  match hdef with
  | ⟨φ, hφ⟩ =>
    -- the "liar" formula `¬ φ(x₀)` and its own Gödel number
    let ψ : AForm := .not φ
    let c : Nat := code ψ
    let v : Nat → Nat := fun _ => c
    have hv0 : v 0 = c := rfl
    have h1 : ψ.Sat v ↔ ¬ ArithTruth code c c := by
      show ¬ φ.Sat v ↔ ¬ ArithTruth code c c
      rw [hφ v, hv0]
    have h2 : ArithTruth code c c ↔ ψ.Sat v := by
      constructor
      · intro hex
        match hex with
        | ⟨χ, hχ, hsat⟩ =>
          have hχψ : χ = ψ := hcode hχ
          exact hχψ ▸ hsat
      · intro h
        exact ⟨ψ, rfl, h⟩
    by_cases hs : ψ.Sat v
    · exact h1.mp hs (h2.mpr hs)
    · exact hs (h2.mp (Classical.byContradiction fun hnT => hs (h1.mpr hnT)))

/-- **Tarski's undefinability theorem** (semantic form).  Let `code` be any injective Gödel
numbering of the formulas of first-order arithmetic.  Then arithmetical truth — the
satisfaction relation `ArithTruth code` of the standard model `Nat` — is *not* arithmetically
definable: there is no arithmetical formula `T(x₀, x₁)` expressing "the arithmetical formula
with Gödel number `x₀` is true of `x₁`". -/
theorem Tarski_undefinability (code : AForm → Nat) (hcode : Function.Injective code) :
    ¬ ArithDefinableRel (ArithTruth code) := by
  intro hdef
  match hdef with
  | ⟨T, hT⟩ =>
    refine diagonal_truth_not_ArithDefinable code hcode ⟨selfApply T, fun v => ?_⟩
    have h0 : upd v 1 (v 0) 0 = v 0 := by simp [upd]
    have h1 : upd v 1 (v 0) 1 = v 0 := by simp [upd]
    rw [selfApply_sat T v, hT (upd v 1 (v 0)), h0, h1]

end Frontier

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

