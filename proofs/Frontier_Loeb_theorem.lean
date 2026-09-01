/-
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- An abstract axiomatization of a formal theory (think: Peano Arithmetic) together with
its provability predicate `□`.

* `Sentence` is the type of sentences of the theory;
* `imp` is the implication connective;
* `box φ` is the (internalized) sentence "`φ` is provable in the theory";
* `Thm φ` says that `φ` is a theorem of the theory (`PA ⊢ φ`).

The axioms are the standard ones needed for Löb's theorem:

* closure of `Thm` under modus ponens, and the implicational axioms `K` and `S`
  (so the theory proves all tautologies of implicational propositional logic);
* the Hilbert–Bernays–Löb derivability conditions:
  `D1` (necessitation), `D2` (distribution of `□` over `→`), `D3` (`□φ → □□φ`);
* the diagonal (fixed point) lemma, which in arithmetic is provided by Gödel's
  self-reference construction. -/
structure ProvabilityTheory where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The provability operator: `box φ` is the sentence "`φ` is provable". -/
  box : Sentence → Sentence
  /-- `Thm φ` means the theory proves `φ`. -/
  Thm : Sentence → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b}, Thm (imp a b) → Thm a → Thm b
  /-- Axiom scheme `K` of implicational logic. -/
  ax_K : ∀ a b, Thm (imp a (imp b a))
  /-- Axiom scheme `S` of implicational logic. -/
  ax_S : ∀ a b c, Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- First derivability condition: necessitation. -/
  D1 : ∀ {a}, Thm a → Thm (box a)
  /-- Second derivability condition: `□(a → b) → (□a → □b)`. -/
  D2 : ∀ a b, Thm (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Third derivability condition: `□a → □□a`. -/
  D3 : ∀ a, Thm (imp (box a) (box (box a)))
  /-- The diagonal lemma: for every `a` there is a sentence `d` which the theory proves
  equivalent to `□d → a`. -/
  diagonal : ∀ a, ∃ d, Thm (imp d (imp (box d) a)) ∧ Thm (imp (imp (box d) a) d)

namespace ProvabilityTheory

variable (T : ProvabilityTheory)

/-- Every sentence implies itself. -/
theorem imp_self' (a : T.Sentence) : T.Thm (T.imp a a) :=
  T.mp (T.mp (T.ax_S a (T.imp a a) a) (T.ax_K a (T.imp a a))) (T.ax_K a a)

/-- If the theory proves `b`, then it proves `a → b`. -/
theorem imp_of (a : T.Sentence) {b : T.Sentence} (hb : T.Thm b) : T.Thm (T.imp a b) :=
  T.mp (T.ax_K b a) hb

/-- Hypothetical syllogism: chaining of provable implications. -/
theorem imp_trans {a b c : T.Sentence} (hab : T.Thm (T.imp a b)) (hbc : T.Thm (T.imp b c)) :
    T.Thm (T.imp a c) :=
  T.mp (T.mp (T.ax_S a b c) (T.imp_of a hbc)) hab

/-- Contraction-style step: from `a → (b → c)` and `a → b` infer `a → c`. -/
theorem imp_mp {a b c : T.Sentence} (h : T.Thm (T.imp a (T.imp b c)))
    (hab : T.Thm (T.imp a b)) : T.Thm (T.imp a c) :=
  T.mp (T.mp (T.ax_S a b c) h) hab

/-- Boxing an implication: from `⊢ a → b` infer `⊢ □a → □b`. -/
theorem box_mono {a b : T.Sentence} (h : T.Thm (T.imp a b)) :
    T.Thm (T.imp (T.box a) (T.box b)) :=
  T.mp (T.D2 a b) (T.D1 h)

end ProvabilityTheory

/-- **Löb's theorem**.  In any theory satisfying the Hilbert–Bernays–Löb derivability
conditions and the diagonal lemma (e.g. Peano Arithmetic with its standard provability
predicate): if the theory proves `□φ → φ`, then it proves `φ`. -/
theorem Loeb_theorem (T : ProvabilityTheory) (a : T.Sentence)
    (h : T.Thm (T.imp (T.box a) a)) : T.Thm a := by
  obtain ⟨d, hd1, hd2⟩ := T.diagonal a
  -- `⊢ □d → □(□d → a)`
  have h1 : T.Thm (T.imp (T.box d) (T.box (T.imp (T.box d) a))) := T.box_mono hd1
  -- `⊢ □(□d → a) → (□□d → □a)`
  have h2 : T.Thm (T.imp (T.box (T.imp (T.box d) a)) (T.imp (T.box (T.box d)) (T.box a))) :=
    T.D2 (T.box d) a
  -- `⊢ □d → (□□d → □a)`
  have h3 : T.Thm (T.imp (T.box d) (T.imp (T.box (T.box d)) (T.box a))) := T.imp_trans h1 h2
  -- `⊢ □d → □a`, using `D3`
  have h4 : T.Thm (T.imp (T.box d) (T.box a)) := T.imp_mp h3 (T.D3 d)
  -- `⊢ □d → a`, using the hypothesis
  have h5 : T.Thm (T.imp (T.box d) a) := T.imp_trans h4 h
  -- hence `⊢ d`, and by necessitation `⊢ □d`
  have h6 : T.Thm d := T.mp hd2 h5
  have h7 : T.Thm (T.box d) := T.D1 h6
  exact T.mp h5 h7

/-- The hypotheses of `Frontier.Loeb_theorem` are not vacuous, and not trivially satisfied:
there is a `ProvabilityTheory` whose set of theorems is not all sentences. -/
example : ∃ T : ProvabilityTheory, ∃ a : T.Sentence, ¬ T.Thm a := by
  refine ⟨{ Sentence := Prop
            imp := fun p q => p → q
            box := fun _ => True
            Thm := fun p => p
            mp := fun h ha => h ha
            ax_K := fun _ _ => fun ha _ => ha
            ax_S := fun _ _ _ => fun h g x => h x (g x)
            D1 := fun _ => trivial
            D2 := fun _ _ _ _ => trivial
            D3 := fun _ _ => trivial
            diagonal := fun p => ⟨p, fun hp _ => hp, fun h => h trivial⟩ }, False, id⟩

end Frontier

