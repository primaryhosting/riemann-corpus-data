import Mathlib

/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
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

/-!
## Setting

Gödel's second incompleteness theorem states that no consistent, recursively axiomatized
theory `T` extending `PA` proves the arithmetical sentence `Con(T)` expressing its own
consistency.

The theorem is formalized here in the standard *abstract* (Hilbert–Bernays–Löb) form, i.e.
as the Lean-checked reduction of the theorem to the derivability conditions.  The data are:

* `B`, the Lindenbaum–Tarski algebra of `T`: sentences of the language of `T` modulo
  `T`-provable equivalence.  Since `T` extends `PA`, its underlying logic is classical, so `B`
  is a Boolean algebra, and a sentence `a` is *provable in `T`* exactly when its class satisfies
  `a = ⊤`.  Consistency of `T` says precisely that `⊥ ≠ ⊤` in `B`, i.e. that `T` does not
  prove a contradiction.
* `box : B → B`, the provability predicate `a ↦ ⌜Prov_T(⌜a⌝)⌝`.  (For a *recursively
  axiomatized* `T` such a `Σ₁` predicate exists by arithmetization of syntax, and it descends
  to the Lindenbaum algebra because `T ⊢ a ↔ b` implies `T ⊢ □a ↔ □b`.)

The hypotheses `D1`, `D2`, `D3` are the three Hilbert–Bernays–Löb derivability conditions,
which hold for every recursively axiomatized theory extending `PA`:

* `D1`  (necessitation)      `T ⊢ a  ⟹  T ⊢ □a`;
* `D2`  (internal modus ponens) `T ⊢ □(a → b) → (□a → □b)`;
* `D3`  (provable Σ₁-completeness) `T ⊢ □a → □□a`.

Finally `hg` is the Gödel fixed point supplied by the diagonal lemma: a sentence `g` with
`T ⊢ g ↔ ¬□g`.

Note that these hypotheses are satisfiable by a *consistent* system (see
`Frontier.goedel_hypotheses_satisfiable` below), so the theorem below is not vacuous.
-/

section
variable {B : Type*} [BooleanAlgebra B]

/-- The internal consistency statement `Con(T) = ¬ Prov_T(⌜⊥⌝)`, as an element of the
Lindenbaum algebra. -/
def Con (box : B → B) : B := (box ⊥)ᶜ

/-- **Formalized first incompleteness step.**  If `g` is a Gödel fixed point (`T ⊢ g ↔ ¬□g`)
then `T ⊢ □g → □⊥`: the theory proves that provability of its Gödel sentence would make it
inconsistent. -/
theorem box_goedel_le_box_bot (box : B → B)
    (D1 : ∀ a : B, a = ⊤ → box a = ⊤)
    (D2 : ∀ a b : B, box (a ⇨ b) ⊓ box a ≤ box b)
    (D3 : ∀ a : B, box a ≤ box (box a))
    (g : B) (hg : g = (box g)ᶜ) :
    box g ≤ box ⊥ := by
  have h1 : g ≤ box g ⇨ (⊥ : B) := by
    rw [himp_bot]
    exact hg.le
  have h2 : box (g ⇨ (box g ⇨ (⊥ : B))) = ⊤ := D1 _ (himp_eq_top_iff.mpr h1)
  have h3 : box g ≤ box (box g ⇨ (⊥ : B)) := by
    calc box g = box (g ⇨ (box g ⇨ (⊥ : B))) ⊓ box g := by rw [h2, top_inf_eq]
      _ ≤ box (box g ⇨ (⊥ : B)) := D2 _ _
  exact le_trans (le_inf h3 (D3 g)) (D2 _ _)

/-- **Gödel's second incompleteness theorem** (abstract Hilbert–Bernays–Löb form).

Let `B` be the Lindenbaum–Tarski algebra of a theory `T` (so `a = ⊤` means `T ⊢ a`), let
`box` be a provability predicate for `T` satisfying the three derivability conditions
`D1`, `D2`, `D3`, and let `g` be a Gödel fixed point for `box`, as provided by the diagonal
lemma.  If `T` is consistent (`⊥ ≠ ⊤`, i.e. `T ⊬ ⊥`), then `T` does not prove its own
consistency statement `Con(T) = ¬□⊥`.

Every consistent recursively axiomatized theory extending `PA` provides such data, so no such
theory proves its own consistency. -/
theorem Goedel_second_incompleteness (box : B → B)
    (D1 : ∀ a : B, a = ⊤ → box a = ⊤)
    (D2 : ∀ a b : B, box (a ⇨ b) ⊓ box a ≤ box b)
    (D3 : ∀ a : B, box a ≤ box (box a))
    (g : B) (hg : g = (box g)ᶜ)
    (hcon : (⊥ : B) ≠ ⊤) :
    Con box ≠ ⊤ := by
  intro hProvCon
  -- If `T ⊢ Con(T)` then `□⊥` is refutable, i.e. `□⊥ = ⊥` in the Lindenbaum algebra.
  have hbot : box (⊥ : B) = ⊥ := compl_eq_top.mp hProvCon
  -- Hence the Gödel sentence is not provably provable.
  have hboxg : box g = ⊥ :=
    le_bot_iff.mp (hbot ▸ box_goedel_le_box_bot box D1 D2 D3 g hg)
  -- Therefore `T ⊢ g`, ...
  have hgtop : g = ⊤ := by rw [hg, hboxg, compl_bot]
  -- ... so by necessitation `T ⊢ □g`, contradicting `□g = ⊥` in a consistent theory.
  exact hcon (hboxg ▸ D1 g hgtop)

end

/-- The hypotheses of `Frontier.Goedel_second_incompleteness` are satisfiable by a *consistent*
system (here the two-element algebra with `box a = ⊤`), so the theorem is not vacuous: it
really rules out `Con(T) = ⊤` rather than resting on contradictory assumptions. -/
theorem goedel_hypotheses_satisfiable :
    ∃ (box : Prop → Prop) (g : Prop),
      (∀ a : Prop, a = ⊤ → box a = ⊤) ∧
      (∀ a b : Prop, box (a ⇨ b) ⊓ box a ≤ box b) ∧
      (∀ a : Prop, box a ≤ box (box a)) ∧
      g = (box g)ᶜ ∧ (⊥ : Prop) ≠ ⊤ := by
  refine ⟨fun _ => ⊤, ⊥, fun a _ => rfl, fun a b => le_top, fun a => le_top, ?_, ?_⟩
  · simp
  · simp

end Frontier

