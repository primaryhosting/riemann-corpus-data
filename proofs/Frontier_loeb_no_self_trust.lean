import Mathlib

/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- An abstract *provability structure*: a theory `T` over a type of sentences, equipped with
an implication connective, a provability predicate `Prf` ("`T` proves ..."), and an internal
provability operator `box` (the arithmetized provability predicate of `T`).

The axioms are:

* `mp` : the provable sentences are closed under modus ponens;
* `ax_K1`, `ax_K2` : the two Hilbert axiom schemes for implication, so that `T` contains
  (implicational) propositional logic;
* `nec` : necessitation — if `T` proves `A`, then `T` proves `□A`;
* `ax_K` : the distribution axiom `□(A → B) → (□A → □B)`;
* `ax_four` : `□A → □□A`;
* `diag` : the diagonal (fixed point) lemma: for every sentence `A` there is a sentence `F`
  with `T ⊢ F ↔ (□F → A)`.

These are exactly the Hilbert–Bernays–Löb derivability conditions together with the
diagonal lemma, all of which hold e.g. for Peano arithmetic and its provability predicate. -/
structure ProvabilityStructure where
  /-- The type of sentences of the language. -/
  Sent : Type*
  /-- Implication between sentences. -/
  imp : Sent → Sent → Sent
  /-- `Prf A` means: the theory proves the sentence `A`. -/
  Prf : Sent → Prop
  /-- `box A` is the sentence expressing "`A` is provable in the theory". -/
  box : Sent → Sent
  /-- Modus ponens. -/
  mp : ∀ {a b : Sent}, Prf (imp a b) → Prf a → Prf b
  /-- Hilbert axiom scheme `A → (B → A)`. -/
  ax_K1 : ∀ a b : Sent, Prf (imp a (imp b a))
  /-- Hilbert axiom scheme `(A → (B → C)) → ((A → B) → (A → C))`. -/
  ax_K2 : ∀ a b c : Sent, Prf (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Necessitation. -/
  nec : ∀ {a : Sent}, Prf a → Prf (box a)
  /-- Distribution axiom for the provability operator. -/
  ax_K : ∀ a b : Sent, Prf (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Transparency of provability: `□A → □□A`. -/
  ax_four : ∀ a : Sent, Prf (imp (box a) (box (box a)))
  /-- Diagonal lemma. -/
  diag : ∀ a : Sent, ∃ f : Sent,
    Prf (imp f (imp (box f) a)) ∧ Prf (imp (imp (box f) a) f)

namespace ProvabilityStructure

variable (T : ProvabilityStructure)

/-- The derived rule: from `A → (B → C)` and `A → B` infer `A → C`. -/
theorem imp_S {a b c : T.Sent} (h1 : T.Prf (T.imp a (T.imp b c)))
    (h2 : T.Prf (T.imp a b)) : T.Prf (T.imp a c) :=
  T.mp (T.mp (T.ax_K2 a b c) h1) h2

/-- Weakening: from `B` infer `A → B`. -/
theorem imp_weaken {a b : T.Sent} (h : T.Prf b) : T.Prf (T.imp a b) :=
  T.mp (T.ax_K1 b a) h

/-- Syllogism: from `A → B` and `B → C` infer `A → C`. -/
theorem imp_trans {a b c : T.Sent} (h1 : T.Prf (T.imp a b))
    (h2 : T.Prf (T.imp b c)) : T.Prf (T.imp a c) :=
  T.imp_S (T.imp_weaken h2) h1

/-- **Löb's theorem.** If a theory satisfying the derivability conditions and the diagonal
lemma proves the reflection sentence `□A → A`, then it already proves `A`. -/
theorem loeb {a : T.Sent} (h : T.Prf (T.imp (T.box a) a)) : T.Prf a := by
  obtain ⟨f, hf1, hf2⟩ := T.diag a
  -- `□f → □(□f → a)`
  have hB : T.Prf (T.imp (T.box f) (T.box (T.imp (T.box f) a))) :=
    T.mp (T.ax_K f (T.imp (T.box f) a)) (T.nec hf1)
  -- `□(□f → a) → (□□f → □a)`
  have hC : T.Prf (T.imp (T.box (T.imp (T.box f) a))
      (T.imp (T.box (T.box f)) (T.box a))) := T.ax_K (T.box f) a
  -- `□f → (□□f → □a)`
  have hD : T.Prf (T.imp (T.box f) (T.imp (T.box (T.box f)) (T.box a))) :=
    T.imp_trans hB hC
  -- `□f → □a`
  have hF : T.Prf (T.imp (T.box f) (T.box a)) := T.imp_S hD (T.ax_four f)
  -- `□f → a`
  have hG : T.Prf (T.imp (T.box f) a) := T.imp_trans hF h
  -- hence `f`, hence `□f`, hence `a`
  exact T.mp hG (T.nec (T.mp hf2 hG))

end ProvabilityStructure

/-- **No self-trust (Löb).**

A consistent theory cannot prove the reflection principle for a sentence it does not prove:
if the theory `T` (satisfying the Hilbert–Bernays–Löb derivability conditions and the diagonal
lemma) is consistent — witnessed here by some sentence `c` that `T` does not prove — and `a` is
a sentence with `T ⊬ a`, then `T ⊬ (□a → a)`.

Remark: the consistency hypothesis `hcon` is included because it is part of the informal
statement, but it is in fact not needed: `T ⊬ a` already rules out `T ⊢ (□a → a)` by Löb's
theorem. -/
theorem loeb_no_self_trust (T : ProvabilityStructure) {c a : T.Sent}
    (_hcon : ¬ T.Prf c) (ha : ¬ T.Prf a) : ¬ T.Prf (T.imp (T.box a) a) :=
  fun h => ha (T.loeb h)

/-- A concrete consistent provability structure, showing that the hypotheses of
`Frontier.loeb_no_self_trust` are simultaneously satisfiable (so the theorem is not vacuous):
sentences are booleans, `Prf a` means `a = true`, and `□a` is the constant `true`. -/
def boolStructure : ProvabilityStructure where
  Sent := Bool
  imp a b := (!a || b)
  Prf a := a = true
  box _ := true
  mp := by decide
  ax_K1 := by decide
  ax_K2 := by decide
  nec := by decide
  ax_K := by decide
  ax_four := by decide
  diag a := ⟨a, by revert a; decide, by revert a; decide⟩

/-- In `Frontier.boolStructure` the sentence `false` is unprovable (the structure is
consistent), hence by `Frontier.loeb_no_self_trust` the reflection sentence `□false → false`
is not provable there either. -/
example : ¬ boolStructure.Prf (boolStructure.imp (boolStructure.box false) false) :=
  loeb_no_self_trust boolStructure (c := false)
    (by simp [boolStructure]) (by simp [boolStructure])

end Frontier

