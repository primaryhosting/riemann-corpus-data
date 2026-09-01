import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The *local constellation count* of the shift pattern (constellation) `h : Fin k → ℤ`
relative to a set `S` of integers, counted over the window `I`:
the number of `x ∈ I` such that all the shifted points `x + h i` lie in `S`. -/
def constLocalCount {k : ℕ} (S I : Finset ℤ) (h : Fin k → ℤ) : ℕ :=
  (I.filter (fun x => ∀ i : Fin k, x + h i ∈ S)).card

/-- `k = 1`: the local count of a one-point constellation. -/
theorem constLocalCount_one (S I : Finset ℤ) (h0 : ℤ) :
    constLocalCount S I ![h0] = (I.filter (fun x => x + h0 ∈ S)).card := by
  unfold constLocalCount
  congr 1
  apply Finset.filter_congr
  intro x _
  simp

/-- `k = 2`: the local count of a two-point constellation. -/
theorem constLocalCount_two (S I : Finset ℤ) (h0 h1 : ℤ) :
    constLocalCount S I ![h0, h1] =
      (I.filter (fun x => x + h0 ∈ S ∧ x + h1 ∈ S)).card := by
  unfold constLocalCount
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [Fin.forall_fin_two]

/-- `k = 3`: the local count of a three-point constellation, unfolded. -/
theorem constLocalCount_three (S I : Finset ℤ) (h0 h1 h2 : ℤ) :
    constLocalCount S I ![h0, h1, h2] =
      (I.filter (fun x => x + h0 ∈ S ∧ x + h1 ∈ S ∧ x + h2 ∈ S)).card := by
  unfold constLocalCount
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · intro hx
    exact ⟨hx 0, hx 1, hx 2⟩
  · intro hx i
    fin_cases i
    · exact hx.1
    · exact hx.2.1
    · exact hx.2.2

/-- Bonferroni step: intersecting with one more condition loses at most the number of
elements of the window failing that condition. -/
theorem card_filter_and_ge (I : Finset ℤ) (p q : ℤ → Prop)
    [DecidablePred p] [DecidablePred q] :
    (I.filter p).card + (I.filter q).card ≤
      (I.filter (fun x => p x ∧ q x)).card + I.card := by
  classical
  have hinter : I.filter p ∩ I.filter q = I.filter (fun x => p x ∧ q x) := by
    ext x; simp [and_assoc, and_left_comm, and_comm]
  have hunion : (I.filter p ∪ I.filter q) ⊆ I := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx <;> exact Finset.mem_filter.mp hx |>.1
  have hkey := Finset.card_inter_add_card_union (I.filter p) (I.filter q)
  have hle : (I.filter p ∪ I.filter q).card ≤ I.card := Finset.card_le_card hunion
  rw [hinter] at hkey
  omega

/-- Monotonicity: adding a point to the constellation can only decrease the local count. -/
theorem constLocalCount_three_le_two (S I : Finset ℤ) (h0 h1 h2 : ℤ) :
    constLocalCount S I ![h0, h1, h2] ≤ constLocalCount S I ![h0, h1] := by
  rw [constLocalCount_three, constLocalCount_two]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

/--
**Constellation local count, `k = 3`.**

For a set `S ⊆ ℤ`, a window `I ⊆ ℤ` and a three-point constellation `(h₀, h₁, h₂)`:

1. the local count is exactly the number of `x ∈ I` with `x + h₀, x + h₁, x + h₂ ∈ S`;
2. it is bounded above by the corresponding two-point (and hence one-point) local counts;
3. (Bonferroni / union bound) it is bounded below by the sum of the three one-point
   local counts minus twice the size of the window.
-/
theorem ConstellationLocalCountK3 (S I : Finset ℤ) (h0 h1 h2 : ℤ) :
    constLocalCount S I ![h0, h1, h2] =
        (I.filter (fun x => x + h0 ∈ S ∧ x + h1 ∈ S ∧ x + h2 ∈ S)).card ∧
      constLocalCount S I ![h0, h1, h2] ≤ constLocalCount S I ![h0, h1] ∧
      constLocalCount S I ![h0, h1] ≤ constLocalCount S I ![h0] ∧
      (I.filter (fun x => x + h0 ∈ S)).card + (I.filter (fun x => x + h1 ∈ S)).card
          + (I.filter (fun x => x + h2 ∈ S)).card
        ≤ constLocalCount S I ![h0, h1, h2] + 2 * I.card := by
  classical
  refine ⟨constLocalCount_three S I h0 h1 h2, constLocalCount_three_le_two S I h0 h1 h2, ?_, ?_⟩
  · rw [constLocalCount_two, constLocalCount_one]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  · have h12 := card_filter_and_ge I (fun x => x + h0 ∈ S) (fun x => x + h1 ∈ S)
    have h123 := card_filter_and_ge I (fun x => x + h0 ∈ S ∧ x + h1 ∈ S)
      (fun x => x + h2 ∈ S)
    rw [constLocalCount_three]
    have hrw : (I.filter (fun x => (x + h0 ∈ S ∧ x + h1 ∈ S) ∧ x + h2 ∈ S)).card
        = (I.filter (fun x => x + h0 ∈ S ∧ x + h1 ∈ S ∧ x + h2 ∈ S)).card := by
      congr 1
      apply Finset.filter_congr
      intro x _
      simp [and_assoc]
    rw [hrw] at h123
    omega

end Brockian

