/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

For a finite set of integer shifts `H = {h₁, …, h_k}` (a *constellation pattern*) and a
modulus `p`, the *local count* is the number of residue classes `a` mod `p` such that all
the shifted values `a + hᵢ` are nonzero mod `p`; this is the local factor appearing in the
Hardy–Littlewood singular series for prime constellations.

The general formula `localCount p H = p - #(H mod p)` is proved as `Brockian.localCount_eq`
(via `Finset.card_compl`, `Finset.card_image_of_injective` and `neg_injective`), and the
main result specialises it to `k = 3`.
-/

namespace Brockian

open Finset

/-- The local count of an integer constellation `H = {h₁, …, h_k}` at the modulus `p`:
the number of residues `a` modulo `p` for which none of the shifted values `a + hᵢ`
vanishes modulo `p`. -/
def localCount (p : ℕ) [NeZero p] (H : Finset ℤ) : ℕ :=
  (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card

/-- The residues excluded by the constellation `H` are exactly the negatives of the
reductions of the shifts. -/
lemma compl_good_set (p : ℕ) [NeZero p] (H : Finset ℤ) :
    (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0))ᶜ
      = H.image (fun h : ℤ => -(h : ZMod p)) := by
  classical
  ext a
  simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    not_forall, not_not]
  constructor
  · rintro ⟨h, hH, ha⟩
    exact ⟨h, hH, by linear_combination -ha⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by ring⟩

/-- Negating does not change the number of distinct reductions of the shifts. -/
lemma card_image_neg_cast (p : ℕ) [NeZero p] (H : Finset ℤ) :
    (H.image (fun h : ℤ => -(h : ZMod p))).card = (H.image (fun h : ℤ => (h : ZMod p))).card := by
  classical
  have : H.image (fun h : ℤ => -(h : ZMod p))
      = (H.image (fun h : ℤ => (h : ZMod p))).image (fun x : ZMod p => -x) := by
    rw [Finset.image_image]
    rfl
  rw [this, Finset.card_image_of_injective _ neg_injective]

/-- **General local count formula.**  `localCount p H = p - #(H mod p)`. -/
lemma localCount_eq (p : ℕ) [NeZero p] (H : Finset ℤ) :
    localCount p H = p - (H.image (fun h : ℤ => (h : ZMod p))).card := by
  classical
  have hcompl := congrArg Finset.card (compl_good_set p H)
  rw [Finset.card_compl, ZMod.card, card_image_neg_cast] at hcompl
  have hle : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ p := by
    calc (H.image (fun h : ℤ => (h : ZMod p))).card
        ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  have hlc : localCount p H ≤ p := by
    unfold localCount
    calc (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card
        ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  unfold localCount at *
  omega

/-- The reduction mod `p` of a three-element constellation has exactly three elements
when the shifts are pairwise incongruent. -/
lemma card_image_triple (p : ℕ) [NeZero p] (h₁ h₂ h₃ : ℤ)
    (h12 : ¬ h₁ ≡ h₂ [ZMOD (p : ℤ)]) (h13 : ¬ h₁ ≡ h₃ [ZMOD (p : ℤ)])
    (h23 : ¬ h₂ ≡ h₃ [ZMOD (p : ℤ)]) :
    ((({h₁, h₂, h₃} : Finset ℤ)).image (fun h : ℤ => (h : ZMod p))).card = 3 := by
  classical
  have e12 : ((h₁ : ZMod p)) ≠ (h₂ : ZMod p) := fun h => h12 ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  have e13 : ((h₁ : ZMod p)) ≠ (h₃ : ZMod p) := fun h => h13 ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  have e23 : ((h₂ : ZMod p)) ≠ (h₃ : ZMod p) := fun h => h23 ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  rw [Finset.card_insert_of_notMem (by simp [e12, e13]),
    Finset.card_insert_of_notMem (by simp [e23]), Finset.card_singleton]

/-- **Constellation local count, `k = 3`.**  If the three shifts are pairwise
incongruent modulo `p`, then exactly `p - 3` residue classes modulo `p` give a
constellation `(a + h₁, a + h₂, a + h₃)` all of whose members are nonzero modulo `p`. -/
theorem ConstellationLocalCountK3 (p : ℕ) [NeZero p] (h₁ h₂ h₃ : ℤ)
    (h12 : ¬ h₁ ≡ h₂ [ZMOD (p : ℤ)]) (h13 : ¬ h₁ ≡ h₃ [ZMOD (p : ℤ)])
    (h23 : ¬ h₂ ≡ h₃ [ZMOD (p : ℤ)]) :
    localCount p {h₁, h₂, h₃} = p - 3 := by
  rw [localCount_eq, card_image_triple p h₁ h₂ h₃ h12 h13 h23]

/-- A concrete instance, confirming the hypotheses of `ConstellationLocalCountK3` are
satisfiable: the pattern `{0, 2, 6}` leaves exactly `5 - 3 = 2` admissible residues mod `5`. -/
example : localCount 5 {0, 2, 6} = 5 - 3 :=
  ConstellationLocalCountK3 5 0 2 6 (by decide) (by decide) (by decide)

end Brockian

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

