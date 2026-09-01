/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the integers of `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (H.image (fun h : ℤ => (Int.cast h : ZMod p))).card

/-- A finite set of integers is *admissible* if for every prime `p` it misses at least one
residue class modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop := ∀ p : ℕ, p.Prime → nu p H < p

/-- The local factor at the prime `p` of the Hardy–Littlewood singular series of the tuple `H`:
`(1 - ν_p(H)/p) / (1 - 1/p)^{|H|}`. -/
noncomputable def singularFactor (p : ℕ) (H : Finset ℤ) : ℝ :=
  (1 - (nu p H : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

/-- The gap pattern under consideration: the triple `{0, 1350, 1360}`, i.e. the gap ranges
`1350` and `1360` from the origin (internal gap `10`). -/
def gapSet : Finset ℤ := {0, 1350, 1360}

lemma nu_le_card (p : ℕ) (H : Finset ℤ) : nu p H ≤ H.card := Finset.card_image_le

lemma gapSet_card : gapSet.card = 3 := by decide

lemma nu_two_gapSet : nu 2 gapSet = 1 := by decide

lemma nu_three_gapSet : nu 3 gapSet = 2 := by decide

/-- Positivity of every local factor of an admissible tuple. -/
lemma singularFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < singularFactor p H := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnum : 0 < 1 - (nu p H : ℝ) / p := by
    have : (nu p H : ℝ) < (p : ℝ) := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).2 this
    linarith
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]; linarith
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- General admissibility criterion for a triple: it suffices to check the primes `2` and `3`,
since a set of three integers can never cover all residues modulo a prime `p ≥ 5`. -/
lemma admissible_of_card_three {H : Finset ℤ} (hcard : H.card = 3)
    (h2 : nu 2 H < 2) (h3 : nu 3 H < 3) : Admissible H := by
  intro p hp
  rcases lt_or_ge p 5 with hlt | hge
  · interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact h2
    · exact h3
    · exact absurd hp (by decide)
  · calc nu p H ≤ H.card := nu_le_card _ _
      _ = 3 := hcard
      _ < p := by omega

/-- **Singular Series Gaps 13501360.**  The triple `{0, 1350, 1360}` is an admissible
prime-gap pattern: it has three elements, it omits a residue class modulo every prime, and
consequently every local factor of its Hardy–Littlewood singular series is strictly positive. -/
theorem SingularSeriesGaps13501360 :
    gapSet.card = 3 ∧ Admissible gapSet ∧ ∀ p : ℕ, p.Prime → 0 < singularFactor p gapSet := by
  have hadm : Admissible gapSet :=
    admissible_of_card_three gapSet_card (by simp [nu_two_gapSet]) (by simp [nu_three_gapSet])
  exact ⟨gapSet_card, hadm, fun p hp => singularFactor_pos hadm hp⟩

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

