import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-!
## Setting

We work with the standard `m`-fold dilated `n`-dimensional simplex

  `Δ = { v : ℕ^{n+1} | v 0 + ... + v n = m }`

described in *partial sum coordinates*: a vertex is encoded by the function
`s : ℕ → ℕ` with `s j = v 0 + ... + v (j-1)`, so that `s 0 = 0`, `s` is monotone,
and `s j = m` for `j > n`.  The barycentric coordinate `v i` is `s (i+1) - s i`.

The triangulation is the classical Freudenthal–Kuhn triangulation: a maximal cell
is given by a base vertex `s` together with an ordering of the `n` coordinates
`1, …, n`; the ordering is encoded by the function `p : ℕ → ℕ` sending a coordinate
`j ∈ [1,n]` to the step `p j ∈ [0,n-1]` at which it is incremented.  The `k`-th
vertex of the cell is then `wv n s p k`.
-/

/-- `Reg n m s` says that `s` encodes a vertex of the `m`-fold dilated standard
`n`-simplex, in partial sum coordinates. -/
def Reg (n m : ℕ) (s : ℕ → ℕ) : Prop :=
  s 0 = 0 ∧ (∀ j ≤ n, s j ≤ s (j + 1)) ∧ (∀ j, n < j → s j = m)

/-- `IsPos n p` says that `p` restricted to `[1,n]` is an injection into `[0,n-1]`
(hence a bijection), normalised to take the value `n` outside `[1,n]`. -/
def IsPos (n : ℕ) (p : ℕ → ℕ) : Prop :=
  (∀ j, 1 ≤ j → j ≤ n → p j < n) ∧
  (∀ j j', 1 ≤ j → j ≤ n → 1 ≤ j' → j' ≤ n → p j = p j' → j = j') ∧
  (∀ j, (j = 0 ∨ n < j) → p j = n)

/-- The `k`-th vertex of the cell with base point `s` and coordinate ordering `p`. -/
def wv (n : ℕ) (s p : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  fun j => s j + (if 1 ≤ j ∧ j ≤ n ∧ p j < k then 1 else 0)

/-- `IsCell n m s p` says that `(s, p)` describes a cell of the Freudenthal–Kuhn
triangulation of the `m`-fold dilated standard `n`-simplex. -/
def IsCell (n m : ℕ) (s p : ℕ → ℕ) : Prop :=
  Reg n m s ∧ IsPos n p ∧ ∀ k ≤ n, Reg n m (wv n s p k)

/-- A Sperner colouring: the colour of a vertex is one of the `n+1` colours
`0, …, n`, and a vertex may only receive colour `i` if its `i`-th barycentric
coordinate is positive. -/
def SpernerColoring (n m : ℕ) (c : (ℕ → ℕ) → ℕ) : Prop :=
  ∀ s, Reg n m s → c s ≤ n ∧ s (c s) < s (c s + 1)

/-- A cell is *rainbow* if its `n+1` vertices carry all `n+1` colours. -/
def IsRainbowCell (n m : ℕ) (c : (ℕ → ℕ) → ℕ) (s p : ℕ → ℕ) : Prop :=
  IsCell n m s p ∧ ∀ i ≤ n, ∃ k ≤ n, c (wv n s p k) = i

/-!
## Basic facts about `Reg`
-/

lemma Reg.mono {n m : ℕ} {s : ℕ → ℕ} (h : Reg n m s) : Monotone s := by
  refine monotone_nat_of_le_succ (fun j => ?_)
  rcases (by omega : j ≤ n ∨ n < j) with hj | hj
  · exact h.2.1 j hj
  · rw [h.2.2 j hj, h.2.2 (j+1) (by omega)]

lemma Reg.le_top {n m : ℕ} {s : ℕ → ℕ} (h : Reg n m s) (j : ℕ) : s j ≤ m := by
  rcases (by omega : j ≤ n + 1 ∨ n + 1 < j) with hj | hj
  · have h1 : s j ≤ s (n+1) := h.mono hj
    rwa [h.2.2 (n+1) (by omega)] at h1
  · rw [h.2.2 j (by omega)]

lemma Reg.eq_top {n m : ℕ} {s : ℕ → ℕ} (h : Reg n m s) : s (n+1) = m := h.2.2 _ (by omega)

/-!
## Basic facts about `IsPos`
-/

lemma IsPos.surj {n : ℕ} {p : ℕ → ℕ} (h : IsPos n p) {i : ℕ} (hi : i < n) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ p j = i := by
  classical
  have hsub : (Finset.Icc 1 n).image p ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hx
    exact Finset.mem_range.2 (h.1 j hj1 hj2)
  have hcard : ((Finset.Icc 1 n).image p).card = n := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      exact h.2.1 a b ha.1 ha.2 hb.1 hb.2 hab
  have heq : (Finset.Icc 1 n).image p = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have : i ∈ (Finset.Icc 1 n).image p := by rw [heq]; exact Finset.mem_range.2 hi
  simp only [Finset.mem_image, Finset.mem_Icc] at this
  obtain ⟨j, ⟨hj1, hj2⟩, hj⟩ := this
  exact ⟨j, hj1, hj2, hj⟩

/-!
## Basic facts about the vertices of a cell
-/

lemma wv_zero (n : ℕ) (s p : ℕ → ℕ) : wv n s p 0 = s := by
  funext j; simp [wv]

lemma wv_out {n : ℕ} {s p : ℕ → ℕ} {k j : ℕ} (hj : j = 0 ∨ n < j) : wv n s p k j = s j := by
  simp only [wv]
  rw [if_neg]
  · omega
  · omega

lemma wv_in {n : ℕ} {s p : ℕ → ℕ} {k j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    wv n s p k j = s j + (if p j < k then 1 else 0) := by
  simp only [wv]
  by_cases h : p j < k <;> simp [h, hj1, hj2]

/-- The combinatorial criterion for `(s,p)` to be a cell. -/
lemma isCell_iff {n m : ℕ} {s p : ℕ → ℕ} (hs : Reg n m s) (hp : IsPos n p) :
    IsCell n m s p ↔ ∀ j, 1 ≤ j → j ≤ n → s j = s (j+1) → (j < n ∧ p (j+1) < p j) := by
  constructor
  · rintro ⟨-, -, hcell⟩ j hj1 hj2 hsj
    have hjn : j < n := by
      by_contra hcon
      have hjn : j = n := by omega
      have hk : p j + 1 ≤ n := hp.1 j hj1 hj2
      have := (hcell (p j + 1) hk).2.1 j hj2
      rw [wv_in hj1 hj2, wv_out (Or.inr (show n < j + 1 by omega))] at this
      rw [if_pos (by omega)] at this
      omega
    refine ⟨hjn, ?_⟩
    by_contra hcon
    have hne : p (j+1) ≠ p j := fun hh => by
      have := hp.2.1 (j+1) j (by omega) (by omega) hj1 hj2 hh; omega
    have hlt : p j < p (j+1) := by omega
    have hk : p j + 1 ≤ n := by have := hp.1 (j+1) (by omega) (by omega); omega
    have := (hcell (p j + 1) hk).2.1 j hj2
    rw [wv_in hj1 hj2, wv_in (by omega) (by omega)] at this
    rw [if_pos (by omega), if_neg (by omega)] at this
    omega
  · intro hcrit
    refine ⟨hs, hp, fun k hk => ⟨?_, ?_, ?_⟩⟩
    · rw [wv_out (Or.inl rfl)]; exact hs.1
    · intro j hj
      rcases (by omega : j = 0 ∨ 1 ≤ j) with rfl | hj1
      · rw [wv_out (Or.inl rfl), hs.1]; omega
      · rw [wv_in hj1 hj]
        rcases (by omega : j = n ∨ j + 1 ≤ n) with hjn | hj2
        · rw [wv_out (Or.inr (show n < j + 1 by omega))]
          have hmono := hs.2.1 j hj
          have : s j ≠ s (j+1) := by
            intro hh; have := (hcrit j hj1 hj hh).1; omega
          split <;> omega
        · rw [wv_in (by omega) hj2]
          have hmono := hs.2.1 j hj
          by_cases h1 : p j < k
          · by_cases h2 : p (j+1) < k
            · simp [h1, h2]; omega
            · have : s j ≠ s (j+1) := by
                intro hh; have := (hcrit j hj1 hj hh).2; omega
              simp [h1, h2]; omega
          · simp [h1]; split <;> omega
    · intro j hj
      rw [wv_out (Or.inr hj)]; exact hs.2.2 j hj

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

