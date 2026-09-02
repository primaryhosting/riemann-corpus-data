import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary relation `∈`. -/
inductive setRel : ℕ → Type
  | mem : setRel 2
  deriving DecidableEq

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/
def LSet : Language := ⟨fun _ => Empty, setRel⟩

/-- The membership relation symbol. -/
abbrev memRel : LSet.Relations 2 := setRel.mem

/-- `t₁ ∈' t₂` as a bounded formula of the language of set theory. -/
abbrev memF {n : ℕ} (t₁ t₂ : LSet.Term (Empty ⊕ Fin n)) : LSet.BoundedFormula Empty n :=
  memRel.boundedFormula₂ t₁ t₂

/-! ## The axioms of ZFC -/

/-- Extensionality: `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
def axExt : LSet.Sentence :=
  ∀' ∀' ((∀' (memF &2 &0 ⇔ memF &2 &1)) ⟹ &0 =' &1)

/-- Empty set: `∃ x, ∀ y, y ∉ x`. -/
def axEmpty : LSet.Sentence :=
  ∃' ∀' ∼(memF &1 &0)

/-- Pairing: `∀ x y, ∃ z, ∀ w, w ∈ z ↔ (w = x ∨ w = y)`. -/
def axPair : LSet.Sentence :=
  ∀' ∀' ∃' ∀' (memF &3 &2 ⇔ (&3 =' &0 ⊔ &3 =' &1))

/-- Union: `∀ x, ∃ u, ∀ w, w ∈ u ↔ ∃ v, v ∈ x ∧ w ∈ v`. -/
def axUnion : LSet.Sentence :=
  ∀' ∃' ∀' (memF &2 &1 ⇔ ∃' (memF &3 &0 ⊓ memF &2 &3))

/-- Power set: `∀ x, ∃ p, ∀ y, y ∈ p ↔ ∀ z, z ∈ y → z ∈ x`. -/
def axPowerset : LSet.Sentence :=
  ∀' ∃' ∀' (memF &2 &1 ⇔ ∀' (memF &3 &2 ⟹ memF &3 &0))

/-- Infinity: there is a set containing the empty set and closed under `y ↦ y ∪ {y}`. -/
def axInfinity : LSet.Sentence :=
  ∃' ((∃' (memF &1 &0 ⊓ ∀' ∼(memF &2 &1))) ⊓
      ∀' (memF &1 &0 ⟹ ∃' (memF &2 &0 ⊓ ∀' (memF &3 &2 ⇔ (memF &3 &1 ⊔ &3 =' &1)))))

/-- Foundation: every nonempty set has an `∈`-minimal element. -/
def axFoundation : LSet.Sentence :=
  ∀' ((∃' (memF &1 &0)) ⟹ ∃' (memF &1 &0 ⊓ ∼(∃' (memF &2 &1 ⊓ memF &2 &0))))

/-- Choice (Zermelo's form): every set of pairwise disjoint nonempty sets has a
transversal, i.e. a set meeting each of its members in exactly one point. -/
def axChoice : LSet.Sentence :=
  ∀' (((∀' (memF &1 &0 ⟹ ∃' (memF &2 &1))) ⊓
        (∀' (memF &1 &0 ⟹ ∀' (memF &2 &0 ⟹
          (∃' (memF &3 &1 ⊓ memF &3 &2) ⟹ &1 =' &2))))) ⟹
    ∃' ∀' (memF &2 &0 ⟹ ∃' ((memF &3 &2 ⊓ memF &3 &1) ⊓
      ∀' ((memF &4 &2 ⊓ memF &4 &1) ⟹ &4 =' &3))))

/-! ## The intended structure on `ZFSet` -/

/-- `ZFSet` is a structure for the language of set theory, with `∈` interpreted as membership. -/
instance zfStruc : LSet.Structure ZFSet.{0} where
  funMap := fun {_} f => nomatch f
  RelMap := fun {n} r => match n, r with
    | 2, setRel.mem => fun x => x 0 ∈ x 1

@[simp]
lemma relMap_mem (x : Fin 2 → ZFSet.{0}) :
    Structure.RelMap (L := LSet) (M := ZFSet.{0}) memRel x ↔ x 0 ∈ x 1 := Iff.rfl

@[simp]
lemma realize_memF {n : ℕ} (t₁ t₂ : LSet.Term (Empty ⊕ Fin n)) (v : Empty → ZFSet.{0})
    (xs : Fin n → ZFSet.{0}) :
    (memF t₁ t₂).Realize v xs ↔
      t₁.realize (Sum.elim v xs) ∈ t₂.realize (Sum.elim v xs) := by
  simp [memF, BoundedFormula.realize_rel₂]

example : ZFSet.{0} ⊨ axExt := by
  simp [axExt, Sentence.Realize, Formula.Realize, Fin.snoc]
  intro x y h
  exact ZFSet.ext h

end Frontier

