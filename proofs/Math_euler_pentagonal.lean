/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-! ## Shifting maps -/

/-- `shiftUp c i` is `i + 1` if `c ≤ i`, and `i` otherwise. -/
def shiftUp (c i : ℕ) : ℕ := if c ≤ i then i + 1 else i

/-- `shiftDn c i` is `i - 1` if `c ≤ i`, and `i` otherwise. -/
def shiftDn (c i : ℕ) : ℕ := if c ≤ i then i - 1 else i

lemma shiftUp_injective (c : ℕ) : Function.Injective (shiftUp c) := by
  intro a b h
  unfold shiftUp at h
  split_ifs at h <;> omega

lemma mem_image_shiftUp {c : ℕ} {X : Finset ℕ} {i : ℕ} :
    i ∈ X.image (shiftUp c) ↔ (i < c ∧ i ∈ X) ∨ (c < i ∧ i - 1 ∈ X) := by
  simp only [Finset.mem_image, shiftUp]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h : c ≤ j
    · simp only [h, if_pos]
      right
      refine ⟨by omega, by simpa using hj⟩
    · simp only [h, if_neg, not_false_iff]
      exact Or.inl ⟨Nat.not_le.mp h, hj⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨i, h2, by simp [Nat.not_le.2 h1]⟩
    · refine ⟨i - 1, h2, ?_⟩
      have hci : c ≤ i - 1 := by omega
      rw [if_pos hci]
      omega

lemma shiftDn_injOn {c : ℕ} {X : Finset ℕ} (hc : 1 ≤ c) (h : c - 1 ∉ X) :
    Set.InjOn (shiftDn c) X := by
  intro a ha b hb hab
  simp only [shiftDn] at hab
  split_ifs at hab with h1 h2 h2
  · omega
  · exfalso
    apply h
    have hb' : b = c - 1 := by omega
    rw [← hb']
    simpa using hb
  · exfalso
    apply h
    have ha' : a = c - 1 := by omega
    rw [← ha']
    simpa using ha
  · exact hab

lemma mem_image_shiftDn {c : ℕ} {X : Finset ℕ} {i : ℕ} :
    i ∈ X.image (shiftDn c) ↔ (i < c ∧ i ∈ X) ∨ (c ≤ i + 1 ∧ i + 1 ∈ X) := by
  simp only [Finset.mem_image, shiftDn]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h : c ≤ j
    · simp only [h, if_pos]
      right
      constructor
      · omega
      · have : j - 1 + 1 = j := by omega
        rw [this]; exact hj
    · simp only [h, if_neg, not_false_iff]
      exact Or.inl ⟨Nat.not_le.mp h, hj⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨i, h2, by simp [Nat.not_le.2 h1]⟩
    · exact ⟨i + 1, h2, by simp [h1]⟩

/-! ## The staircase (run at the top) -/

/-- `stair S m` is the length of the maximal run `m, m-1, …` of consecutive elements of `S`
starting at `m`. -/
def stair (S : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | (m + 1) => if (m + 1) ∈ S then stair S m + 1 else 0

lemma stair_le (S : Finset ℕ) (m : ℕ) : stair S m ≤ m := by
  induction m with
  | zero => simp [stair]
  | succ k ih =>
      rw [stair]
      split_ifs
      · omega
      · omega

lemma stair_mem (S : Finset ℕ) (m : ℕ) : ∀ i, m - stair S m < i → i ≤ m → i ∈ S := by
  induction m with
  | zero => intro i h1 h2; omega
  | succ k ih =>
      intro i h1 h2
      rw [stair] at h1
      split_ifs at h1 with hk
      · rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact ih i (by have := stair_le S k; omega) (by omega)
        · have : i = k + 1 := by omega
          exact this ▸ hk
      · exfalso; omega

lemma stair_notMem (S : Finset ℕ) (m : ℕ) (h0 : 0 ∉ S) : m - stair S m ∉ S := by
  induction m with
  | zero => simpa [stair] using h0
  | succ k ih =>
      rw [stair]
      split_ifs with hk
      · have : k + 1 - (stair S k + 1) = k - stair S k := by omega
        rw [this]; exact ih
      · simpa using hk

/-- Characterisation of the staircase length. -/
lemma stair_eq_of {S : Finset ℕ} {m j : ℕ} (hj : j ≤ m)
    (h1 : ∀ i, m - j < i → i ≤ m → i ∈ S) (h2 : m - j ∉ S) : stair S m = j := by
  induction j generalizing m with
  | zero =>
      simp only [Nat.sub_zero] at h2
      cases m with
      | zero => simp [stair]
      | succ k => rw [stair]; simp [h2]
  | succ p ih =>
      cases m with
      | zero => omega
      | succ k =>
          have hmem : (k + 1) ∈ S := h1 (k + 1) (by omega) (le_refl _)
          rw [stair, if_pos hmem]
          have : stair S k = p := by
            refine ih (by omega) ?_ ?_
            · intro i hi hik
              exact h1 i (by omega) (by omega)
            · have : k - p = k + 1 - (p + 1) := by omega
              rw [this]; exact h2
          omega

/-- Lower bound for the staircase length. -/
lemma le_stair {S : Finset ℕ} {m j : ℕ} (hj : j ≤ m)
    (h1 : ∀ i, m - j < i → i ≤ m → i ∈ S) : j ≤ stair S m := by
  induction j generalizing m with
  | zero => omega
  | succ p ih =>
      cases m with
      | zero => omega
      | succ k =>
          have hmem : (k + 1) ∈ S := h1 (k + 1) (by omega) (le_refl _)
          rw [stair, if_pos hmem]
          have : p ≤ stair S k := by
            refine ih (by omega) ?_
            intro i hi hik
            exact h1 i (by omega) (by omega)
          omega

end Math

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

