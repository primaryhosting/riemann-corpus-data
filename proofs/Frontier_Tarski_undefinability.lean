/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open FirstOrder Language

namespace Frontier

/-! ## The language of arithmetic and its standard model -/

/-- The function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The (purely functional) first-order language of arithmetic, with symbols `0`, `1`, `+`, `*`. -/
def arith : Language :=
  { Functions := arithFunc, Relations := fun _ => Empty }

/-- The standard model `ℕ` of the language of arithmetic. -/
instance : arith.Structure ℕ where
  funMap {n} f v :=
    match n, f with
    | _, .zero => 0
    | _, .one => 1
    | _, .add => v 0 + v 1
    | _, .mul => v 0 * v 1
  RelMap {_} r _ := r.elim

/-- A set of tuples of naturals is *arithmetical* when it is definable, without parameters,
by a first-order formula in the language of arithmetic interpreted in the standard model. -/
def Arithmetical {α : Type} (s : Set (α → ℕ)) : Prop :=
  (∅ : Set ℕ).Definable arith s

/-- The *arithmetical truth set* associated with a Gödel numbering `enc` of the formulas with
one free variable: it consists of the pairs `(e, n)` such that `e` is the code of a formula
that is true in the standard model when its free variable is interpreted as `n`. -/
def truthSet (enc : arith.Formula (Fin 1) → ℕ) : Set (Fin 2 → ℕ) :=
  {v | ∃ φ : arith.Formula (Fin 1), enc φ = v 0 ∧ φ.Realize (fun _ => v 1)}

instance : Countable ((l : ℕ) × arith.Functions l) := by
  refine ⟨⟨fun p =>
    match p with
    | ⟨_, arithFunc.zero⟩ => 0
    | ⟨_, arithFunc.one⟩ => 1
    | ⟨_, arithFunc.add⟩ => 2
    | ⟨_, arithFunc.mul⟩ => 3, ?_⟩⟩
  rintro ⟨_, f⟩ ⟨_, g⟩ h
  cases f <;> cases g <;> simp_all

instance : Countable ((l : ℕ) × arith.Relations l) :=
  ⟨⟨fun p => p.2.elim, fun p => p.2.elim⟩⟩

instance : Countable arith.Symbols := inferInstanceAs (Countable (_ ⊕ _))

/-! ## Tarski's undefinability theorem -/

/-- **Tarski's undefinability of truth.**  Arithmetical truth is not arithmetically definable:
for every Gödel numbering `enc` of the arithmetical formulas in one free variable, the set of
pairs `(⌜φ⌝, n)` with `φ` true of `n` in the standard model `ℕ` is not definable by any
first-order formula of the language of arithmetic. -/
theorem Tarski_undefinability (enc : arith.Formula (Fin 1) → ℕ)
    (henc : Function.Injective enc) : ¬ Arithmetical (truthSet enc) := by
  intro h
  -- Substituting the same variable in both arguments keeps definability: the diagonal
  -- `{n | (n, n) ∈ truthSet enc}` is arithmetical, hence so is its complement.
  have hdiag : Arithmetical
      ((fun g : Fin 1 → ℕ => g ∘ (fun _ => 0 : Fin 2 → Fin 1)) ⁻¹' truthSet enc) :=
    Set.Definable.preimage_comp _ h
  obtain ⟨ψ, hψ⟩ := Set.empty_definable_iff.1 hdiag.compl
  have key : ψ.Realize (fun _ => enc ψ) ↔
      ¬ ∃ φ : arith.Formula (Fin 1), enc φ = enc ψ ∧ φ.Realize (fun _ => enc ψ) := by
    have := Set.ext_iff.1 hψ (fun _ => enc ψ)
    simpa [truthSet, Set.mem_compl_iff, Function.comp] using this.symm
  have hex : (∃ φ : arith.Formula (Fin 1), enc φ = enc ψ ∧ φ.Realize (fun _ => enc ψ)) ↔
      ψ.Realize (fun _ => enc ψ) := by
    constructor
    · rintro ⟨φ, hφ, hφ'⟩
      rwa [henc hφ] at hφ'
    · exact fun hb => ⟨ψ, rfl, hb⟩
  rw [hex] at key
  exact (not_iff_self key.symm).elim

/-- Since the language of arithmetic is countable, Gödel numberings exist, so Tarski's
theorem is not vacuous: there is a Gödel numbering, and for any such numbering the
arithmetical truth set fails to be arithmetical. -/
theorem exists_godel_numbering_truthSet_not_arithmetical :
    ∃ enc : arith.Formula (Fin 1) → ℕ,
      Function.Injective enc ∧ ¬ Arithmetical (truthSet enc) := by
  obtain ⟨enc, henc⟩ := exists_injective_nat (arith.Formula (Fin 1))
  exact ⟨enc, henc, Tarski_undefinability enc henc⟩

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

