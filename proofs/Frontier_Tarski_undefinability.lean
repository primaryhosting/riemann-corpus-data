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

set_option grind.warning false

/-!
# Tarski's undefinability of truth

This file formalizes Tarski's theorem: *arithmetical truth is not arithmetically definable*.

We work with the first-order language of arithmetic `Frontier.arith`, with signature
`(0, 1, +, *)`, interpreted in its standard model `ℕ`.

* A set `S ⊆ ℕ` is **arithmetical** (`Frontier.Arithmetical`) if there is a formula `phi(x)` of
  the language of arithmetic, with one free variable, such that `n ∈ S ↔ ℕ ⊨ phi(n)`.
  Similarly for binary relations (`Frontier.Arithmetical₂`).

* Fix any enumeration `f : ℕ → arith.Formula (Fin 1)` of the formulas with one free variable
  (such enumerations exist, since the language is countable: see
  `Frontier.exists_surjective_enumeration`). The **arithmetical truth relation** relative to
  this enumeration is
  `Frontier.truthSet f = {(e, n) | ℕ ⊨ (f e)(n)}`,
  i.e. the satisfaction relation "the `e`-th formula is true of `n`".

The theorem `Frontier.Tarski_undefinability` states that, for *every* enumeration `f` of the
formulas, the truth relation `truthSet f` is **not** arithmetical: no single arithmetical
formula `psi(x, y)` can express "the formula with code `x` is true of `y`". This is the standard
coding-free (semantic) form of Tarski's undefinability theorem, and it is proved by
diagonalization.
-/

namespace Frontier

open FirstOrder Language Function

/-- The function symbols of the language of arithmetic: the constants `0` and `1`, and the
binary operations `+` and `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The first-order language of arithmetic, with signature `(0, 1, +, *)` and no relation
symbols. -/
def arith : Language :=
  { Functions := arithFunc
    Relations := fun _ => Empty }

instance (n : ℕ) : IsEmpty (arith.Relations n) := inferInstanceAs (IsEmpty Empty)

/-- The standard model of arithmetic: the natural numbers, with the usual interpretation of
`0`, `1`, `+` and `*`. -/
instance : arith.Structure ℕ where
  funMap
  | .zero, _ => 0
  | .one, _ => 1
  | .add, v => v 0 + v 1
  | .mul, v => v 0 * v 1
  RelMap := fun {_} r => (IsEmpty.false r).elim

instance : Countable (Σ n, arith.Functions n) := by
  refine Function.Injective.countable (f := fun p =>
      match p with
      | ⟨_, .zero⟩ => 0
      | ⟨_, .one⟩ => 1
      | ⟨_, .add⟩ => 2
      | ⟨_, .mul⟩ => (3 : ℕ)) ?_
  rintro ⟨_, (_ | _ | _ | _)⟩ ⟨_, (_ | _ | _ | _)⟩ h <;> simp_all

instance : IsEmpty (Σ n, arith.Relations n) := ⟨fun p => IsEmpty.false p.2⟩

instance : Countable arith.Symbols :=
  inferInstanceAs (Countable ((Σ n, arith.Functions n) ⊕ (Σ n, arith.Relations n)))

/-- A set of natural numbers is *arithmetical* if it is definable in the standard model `ℕ`
by a formula of the language of arithmetic with one free variable. -/
def Arithmetical (S : Set ℕ) : Prop :=
  ∃ phi : arith.Formula (Fin 1), ∀ n : ℕ, n ∈ S ↔ phi.Realize ![n]

/-- A binary relation on natural numbers is *arithmetical* if it is definable in the standard
model `ℕ` by a formula of the language of arithmetic with two free variables. -/
def Arithmetical₂ (S : Set (ℕ × ℕ)) : Prop :=
  ∃ psi : arith.Formula (Fin 2), ∀ e n : ℕ, (e, n) ∈ S ↔ psi.Realize ![e, n]

/-- There exists an enumeration of all arithmetical formulas in one free variable: the language
of arithmetic is countable. -/
theorem exists_surjective_enumeration :
    ∃ f : ℕ → arith.Formula (Fin 1), Surjective f :=
  exists_surjective_nat _

/-- The arithmetical truth (satisfaction) relation relative to an enumeration `f` of the
formulas in one free variable: the pair `(e, n)` belongs to it exactly when the `e`-th formula
is true of `n` in the standard model. -/
def truthSet (f : ℕ → arith.Formula (Fin 1)) : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | (f p.1).Realize ![p.2]}

/-- Diagonal form of Tarski's theorem: for any enumeration `f` of the arithmetical formulas in
one free variable, the diagonal set `{n | ℕ ⊭ (f n)(n)}` is not arithmetical. -/
theorem diagonal_not_arithmetical (f : ℕ → arith.Formula (Fin 1)) (hf : Surjective f) :
    ¬ Arithmetical {n : ℕ | ¬ (f n).Realize ![n]} := by
  rintro ⟨phi, hphi⟩
  obtain ⟨d, hd⟩ := hf phi
  have h := hphi d
  rw [Set.mem_setOf_eq, hd] at h
  tauto

/-- **Tarski's undefinability of truth.** Arithmetical truth is not arithmetically definable:
for every enumeration `f` of the formulas of arithmetic in one free variable, the satisfaction
relation `{(e, n) | ℕ ⊨ (f e)(n)}` is not definable in the standard model of arithmetic by any
formula of the language of arithmetic. -/
theorem Tarski_undefinability (f : ℕ → arith.Formula (Fin 1)) (hf : Surjective f) :
    ¬ Arithmetical₂ (truthSet f) := by
  rintro ⟨psi, hpsi⟩
  -- The diagonal set is defined by the formula `¬ psi(x, x)`, contradicting `diagonal_not_arithmetical`.
  refine diagonal_not_arithmetical f hf ⟨(Formula.relabel (fun _ => 0) psi).not, fun n => ?_⟩
  have hcomp : (![n] : Fin 1 → ℕ) ∘ (fun _ : Fin 2 => (0 : Fin 1)) = ![n, n] := by
    funext i; fin_cases i <;> rfl
  rw [Set.mem_setOf_eq, Formula.realize_not, Formula.realize_relabel, hcomp]
  exact not_congr (hpsi n n)

/-! ### Sanity checks: the notion of an arithmetical set is not degenerate. -/

/-- The set of idempotent naturals is arithmetical, being defined by `x * x = x`. -/
example : Arithmetical {n : ℕ | n * n = n} :=
  ⟨Term.equal (Functions.apply₂ arithFunc.mul (Term.var 0) (Term.var 0)) (Term.var 0), by
    intro n; simp [Formula.Realize, Term.equal, Term.realize, Structure.funMap]⟩

/-- The set of even naturals is arithmetical, being defined by `∃ y, x = y + y`. -/
example : Arithmetical {n : ℕ | ∃ m, n = m + m} :=
  ⟨BoundedFormula.ex (Term.bdEqual (Term.var (Sum.inl 0))
      (Functions.apply₂ arithFunc.add (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0)))), by
    intro n
    simp [Formula.Realize, Term.realize, Structure.funMap, Fin.snoc]⟩

end Frontier

