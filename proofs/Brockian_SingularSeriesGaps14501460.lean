/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (equivalently, its Hardy–Littlewood
singular series `𝔖(H)` is nonzero) when for every prime `p` the elements of `H` fail
to occupy all residue classes modulo `p`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (H.image (· % p)).card < p

/-- The admissible `4`-tuple exhibited inside the gap range `[1450, 1460]`. -/
def gapTuple : Finset ℕ := {1450, 1454, 1456, 1460}

/-- Only primes `p ≤ #H` have to be tested for admissibility. -/
lemma admissible_of_forall_le_card {H : Finset ℕ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → (H.image (· % p)).card < p) :
    Admissible H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · exact lt_of_le_of_lt Finset.card_image_le (by omega)

lemma gapTuple_card : gapTuple.card = 4 := by decide

lemma gapTuple_admissible : Admissible gapTuple := by
  apply admissible_of_forall_le_card
  intro p hp hle
  rw [gapTuple_card] at hle
  have h2 := hp.two_le
  interval_cases p
  · decide
  · decide
  · exact absurd hp (by decide)

/-- Every admissible set inside the gap range `[1450, 1460]` has at most `4` elements:
all its elements share a parity, and they must avoid one residue class modulo `3`. -/
lemma card_le_four_of_admissible {H : Finset ℕ} (hH : H ⊆ Finset.Icc 1450 1460)
    (hA : Admissible H) : H.card ≤ 4 := by
  rcases H.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  -- all elements have the same parity
  have hcard2 : (H.image (· % 2)).card < 2 := hA 2 Nat.prime_two
  have h2 : ∀ y ∈ H, y % 2 = x % 2 := by
    intro y hy
    exact Finset.card_le_one.mp (by omega : (H.image (· % 2)).card ≤ 1)
      (y % 2) (Finset.mem_image_of_mem _ hy) (x % 2) (Finset.mem_image_of_mem _ hx)
  -- some residue class mod 3 is missed
  have hcard3 : (H.image (· % 3)).card < 3 := hA 3 Nat.prime_three
  have hnsub : ¬ (Finset.range 3 ⊆ H.image (· % 3)) := by
    intro hs
    have := Finset.card_le_card hs
    simp only [Finset.card_range] at this
    omega
  obtain ⟨b, hb, hbnot⟩ := Finset.not_subset.mp hnsub
  have hb3 : b < 3 := Finset.mem_range.mp hb
  have h3 : ∀ y ∈ H, y % 3 ≠ b := by
    intro y hy hcon
    exact hbnot (hcon ▸ Finset.mem_image_of_mem _ hy)
  set a := x % 2 with ha
  have ha2 : a < 2 := Nat.mod_lt _ (by norm_num)
  have hsub : H ⊆ (Finset.Icc 1450 1460).filter (fun n => n % 2 = a ∧ n % 3 ≠ b) := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨hH hy, h2 y hy, h3 y hy⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  clear_value a
  clear ha hsub h2 h3 hbnot hnsub hcard2 hcard3 hH hA hb hx
  interval_cases a <;> interval_cases b <;> decide

/-- **Singular Series Gaps 14501460.**

Inside the gap range `[1450, 1460]` the set `{1450, 1454, 1456, 1460}` is admissible
(so its singular series is nonzero: no prime `p` has all of its residue classes occupied),
it has diameter exactly `1460 - 1450 = 10`, and no admissible subset of that range
has more than `4` elements, so this configuration is optimal. -/
theorem SingularSeriesGaps14501460 :
    Admissible gapTuple ∧
    gapTuple ⊆ Finset.Icc 1450 1460 ∧
    gapTuple.card = 4 ∧
    (∀ H : Finset ℕ, H ⊆ Finset.Icc 1450 1460 → Admissible H → H.card ≤ 4) := by
  refine ⟨gapTuple_admissible, by decide, gapTuple_card, ?_⟩
  intro H hH hA
  exact card_le_four_of_admissible hH hA

end Brockian

