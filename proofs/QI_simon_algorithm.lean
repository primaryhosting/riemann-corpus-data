/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced above as a plain block comment: Lean 4 does not allow a
-- module docstring `/-! ... -/` to precede the `import` lines.)

import Mathlib

/-!
## Simon's problem

Simon's problem: a function `f` on `n`-bit strings is promised to be two-to-one with
`f x = f y ↔ y = x ∨ y = x + s` for a hidden nonzero secret `s`; the task is to find `s`.

This file formalises the two information-theoretic facts behind the statement
"Simon's problem takes `O(n)` quantum queries but `Ω(2^(n/2))` classical queries":

* **Quantum side.** Each run of Simon's quantum subroutine returns a uniformly random
  vector `y` in the hyperplane `s^⊥`. We show that `n` such vectors always suffice:
  for every nonzero `s` there is a set `Y` of at most `n` vectors orthogonal to `s`
  such that `s` is the unique nonzero vector orthogonal to all of `Y`. Hence `O(n)`
  quantum queries pin down the secret.

* **Classical side.** A classical algorithm only learns something about `s` when two of
  its queries collide. We show that a query set `Q` that is guaranteed to contain a
  collision for *every* possible secret must satisfy `2 ^ n ≤ Q.card ^ 2`, i.e.
  `Q.card ≥ 2 ^ (n / 2)`. Moreover, if `Q.card ^ 2 + 3 ≤ 2 ^ n`, then there are two
  *different* secrets whose Simon functions agree on `Q` up to a global relabelling of
  the output values, so no classical algorithm making those queries can tell them apart.
-/

namespace QI

open Finset

/-- `n`-bit strings, viewed as vectors over the field with two elements. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The mod-2 inner product of two bit strings. -/
def dotp {n : ℕ} (x y : Bits n) : ZMod 2 := ∑ i, x i * y i

/-- A concrete Simon function with secret `s`, where `j` is a position with `s j = 1`:
its fibers are exactly the pairs `{x, x + s}`. -/
def simonFun {n : ℕ} (s : Bits n) (j : Fin n) (x : Bits n) : Bits n :=
  fun i => x i + x j * s i

/-! ### Basic arithmetic over `ZMod 2` -/

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

private lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

private lemma zmod2_ne_iff {a b : ZMod 2} (h : a ≠ b) : b = a + 1 := by
  revert a b; decide

private lemma zmod2_add_mul (a b c : ZMod 2) : a + c + (b + 1) * c = a + b * c := by
  revert a b c; decide

lemma exists_pivot {n : ℕ} {s : Bits n} (hs : s ≠ 0) : ∃ j, s j = 1 := by
  by_contra h
  push_neg at h
  exact hs (funext fun i => by rcases zmod2_cases (s i) with h0 | h1
                               · exact h0
                               · exact absurd h1 (h i))

/-! ### The Simon function -/

/-- The fibers of `simonFun s j` are exactly the pairs `{x, x + s}`: it is a genuine
Simon function with secret `s`. -/
theorem simonFun_eq_iff {n : ℕ} {s : Bits n} {j : Fin n} (hsj : s j = 1) (x y : Bits n) :
    simonFun s j x = simonFun s j y ↔ (y = x ∨ y = x + s) := by
  constructor
  · intro h
    have h' : ∀ i, x i + x j * s i = y i + y j * s i := fun i => congrFun h i
    by_cases hj : x j = y j
    · left
      funext i
      have hi := h' i
      rw [hj] at hi
      exact (add_right_cancel hi).symm
    · right
      have hyj : y j = x j + 1 := zmod2_ne_iff hj
      funext i
      have hi := h' i
      rw [hyj] at hi
      simp only [Pi.add_apply]
      revert hi
      generalize x i = a
      generalize y i = b
      generalize x j = c
      generalize s i = d
      revert a b c d
      decide
  · rintro (rfl | rfl)
    · rfl
    · funext i
      show x i + x j * s i = (x + s) i + (x + s) j * s i
      simp only [Pi.add_apply, hsj]
      rw [zmod2_add_mul]

/-! ### Quantum side: `n` measurement outcomes determine the secret -/

/-- Given a nonzero secret `s`, there is a set `Y` of at most `n` vectors, all orthogonal to
`s`, such that `s` is the only nonzero vector orthogonal to every element of `Y`.
Since Simon's quantum subroutine returns uniformly random elements of `s^⊥`, this says that
`O(n)` quantum queries suffice to determine `s`. -/
theorem simon_quantum_queries {n : ℕ} {s : Bits n} (hs : s ≠ 0) :
    ∃ Y : Finset (Bits n), Y.card ≤ n ∧ (∀ y ∈ Y, dotp y s = 0) ∧
      ∀ t : Bits n, (∀ y ∈ Y, dotp y t = 0) → t = 0 ∨ t = s := by
  classical
  obtain ⟨j, hj⟩ := exists_pivot hs
  set v : Fin n → Bits n :=
    fun i k => (if k = i then 1 else 0) + s i * (if k = j then 1 else 0) with hv
  have hdot : ∀ (i : Fin n) (t : Bits n), dotp (v i) t = t i + s i * t j := by
    intro i t
    simp [hv, dotp, add_mul, Finset.sum_add_distrib, ite_mul]
  refine ⟨(Finset.univ.erase j).image v, ?_, ?_, ?_⟩
  · refine le_trans Finset.card_image_le ?_
    simp [Finset.card_erase_of_mem]
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    rw [hdot, hj, mul_one, zmod2_add_self]
  · intro t ht
    have key : ∀ i : Fin n, i ≠ j → t i = s i * t j := by
      intro i hi
      have := ht (v i) (Finset.mem_image_of_mem v (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩))
      rw [hdot] at this
      exact zmod2_eq_of_add_eq_zero this
    rcases zmod2_cases (t j) with h0 | h1
    · left
      funext i
      by_cases hi : i = j
      · subst hi; simpa using h0
      · simpa [h0] using key i hi
    · right
      funext i
      by_cases hi : i = j
      · subst hi; rw [h1, hj]
      · simpa [h1] using key i hi

/-! ### Classical side -/

private lemma bits_add_cancel {n : ℕ} (x s : Bits n) : x + (x + s) = s := by
  have hxx : x + x = 0 := funext fun i => zmod2_add_self (x i)
  rw [← add_assoc, hxx, zero_add]

/-- A secret that is ruled out by a collision inside the query set `Q` is a sum of two
distinct elements of `Q`. -/
lemma collision_secret_mem_image {n : ℕ} (Q : Finset (Bits n)) {s : Bits n}
    (h : ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y ∧ y = x + s) :
    s ∈ Q.offDiag.image (fun p : Bits n × Bits n => p.1 + p.2) := by
  classical
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := h
  exact Finset.mem_image.2 ⟨(x, x + s), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, bits_add_cancel x s⟩

lemma card_collision_secrets_le {n : ℕ} (Q : Finset (Bits n)) :
    (Q.offDiag.image (fun p : Bits n × Bits n => p.1 + p.2)).card ≤ Q.card * Q.card - Q.card := by
  classical
  exact le_trans Finset.card_image_le (le_of_eq (Finset.offDiag_card Q))

private lemma card_univ_bits (n : ℕ) : (Finset.univ : Finset (Bits n)).card = 2 ^ n := by
  simp

/-- Any set of queries which is guaranteed to reveal a collision for every possible secret
must have size at least `2 ^ (n / 2)`. -/
theorem simon_classical_lower_bound {n : ℕ} (hn : 1 ≤ n) (Q : Finset (Bits n))
    (h : ∀ s : Bits n, s ≠ 0 → ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y ∧ y = x + s) :
    2 ^ n ≤ Q.card ^ 2 := by
  classical
  have hsub : (Finset.univ : Finset (Bits n)).erase 0 ⊆
      Q.offDiag.image (fun p : Bits n × Bits n => p.1 + p.2) := fun s hs =>
    collision_secret_mem_image Q (h s (Finset.mem_erase.1 hs).1)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ_bits] at hcard
  have hle := card_collision_secrets_le Q
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqq : Q.card ≤ Q.card * Q.card := by
    rcases Nat.eq_zero_or_pos Q.card with h0 | h0
    · simp [h0]
    · exact Nat.le_mul_of_pos_left _ h0
  rcases Nat.eq_zero_or_pos Q.card with h0 | h0
  · exfalso
    rw [h0] at hle
    simp only [Nat.mul_zero, Nat.zero_sub, Nat.le_zero] at hle
    omega
  · rw [pow_two]
    generalize Q.card * Q.card = m at hqq hle ⊢
    generalize (2 : ℕ) ^ n = p at hcard h2 ⊢
    omega

/-- A partial bijection between two sets on which `f` and `g` are injective extends to a
permutation of the whole (finite) type. -/
theorem exists_perm_of_injOn {α : Type*} [DecidableEq α] [Fintype α] (Q : Finset α)
    (f g : α → α) (hf : Set.InjOn f Q) (hg : Set.InjOn g Q) :
    ∃ π : α ≃ α, ∀ x ∈ Q, π (f x) = g x := by
  classical
  have hbij : ∀ (h : α → α), Set.InjOn h Q →
      Function.Bijective (fun x : {x // x ∈ Q} =>
        (⟨h x.1, Finset.mem_image_of_mem h x.2⟩ : {a // a ∈ Q.image h})) := by
    intro h hh
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (hh (by simpa using hx) (by simpa using hy) hxy)
    · rintro ⟨a, ha⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨⟨x, hx⟩, rfl⟩
  let F := Equiv.ofBijective _ (hbij f hf)
  let G := Equiv.ofBijective _ (hbij g hg)
  refine ⟨(F.symm.trans G).extendSubtype, ?_⟩
  intro x hx
  have hfx : f x ∈ Q.image f := Finset.mem_image_of_mem f hx
  rw [Equiv.extendSubtype_apply_of_mem _ _ hfx]
  have hsymm : F.symm ⟨f x, hfx⟩ = ⟨x, hx⟩ := by
    apply F.injective
    simp only [Equiv.apply_symm_apply, F, Equiv.ofBijective_apply]
  simp [Equiv.trans_apply, hsymm, G, Equiv.ofBijective_apply]

/-- Classical indistinguishability: if the query set `Q` satisfies `Q.card ^ 2 + 3 ≤ 2 ^ n`,
then there are two distinct nonzero secrets whose Simon functions agree on `Q` after a global
relabelling `π` of the output values. A classical algorithm making the queries in `Q` therefore
cannot determine the secret. -/
theorem simon_classical_indistinguishable {n : ℕ} (Q : Finset (Bits n))
    (hQ : Q.card ^ 2 + 3 ≤ 2 ^ n) :
    ∃ s₁ s₂ : Bits n, ∃ j₁ j₂ : Fin n, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧ s₁ ≠ s₂ ∧ s₁ j₁ = 1 ∧ s₂ j₂ = 1 ∧
      ∃ π : Bits n ≃ Bits n, ∀ x ∈ Q, π (simonFun s₁ j₁ x) = simonFun s₂ j₂ x := by
  classical
  set G := ((Finset.univ : Finset (Bits n)).erase 0).filter
      (fun s => ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → y ≠ x + s) with hGdef
  have hsub : (Finset.univ : Finset (Bits n)).erase 0 ⊆
      G ∪ Q.offDiag.image (fun p : Bits n × Bits n => p.1 + p.2) := by
    intro s hs
    by_cases hgood : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → y ≠ x + s
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hs, hgood⟩)
    · push_neg at hgood
      obtain ⟨x, hx, y, hy, hxy, hyx⟩ := hgood
      exact Finset.mem_union_right _ (collision_secret_mem_image Q ⟨x, hx, y, hy, hxy, hyx⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ_bits] at hcard
  have hunion := Finset.card_union_le G (Q.offDiag.image (fun p : Bits n × Bits n => p.1 + p.2))
  have hB := card_collision_secrets_le Q
  have hGcard : 1 < G.card := by
    rw [pow_two] at hQ
    generalize Q.card * Q.card = m at hQ hB
    generalize (2 : ℕ) ^ n = p at hQ hcard
    omega
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.1 hGcard
  rw [hGdef, Finset.mem_filter, Finset.mem_erase] at hs₁ hs₂
  obtain ⟨⟨hs₁0, -⟩, hgood₁⟩ := hs₁
  obtain ⟨⟨hs₂0, -⟩, hgood₂⟩ := hs₂
  obtain ⟨j₁, hj₁⟩ := exists_pivot hs₁0
  obtain ⟨j₂, hj₂⟩ := exists_pivot hs₂0
  have hinj : ∀ (s : Bits n) (j : Fin n), s j = 1 → (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → y ≠ x + s) →
      Set.InjOn (simonFun s j) Q := by
    intro s j hj hgood x hx y hy hxy
    by_cases hxy' : x = y
    · exact hxy'
    · exfalso
      rcases (simonFun_eq_iff hj x y).1 hxy with h | h
      · exact hxy' h.symm
      · exact hgood x (by simpa using hx) y (by simpa using hy) hxy' h
  obtain ⟨π, hπ⟩ :=
    exists_perm_of_injOn Q (simonFun s₁ j₁) (simonFun s₂ j₂)
      (hinj s₁ j₁ hj₁ hgood₁) (hinj s₂ j₂ hj₂ hgood₂)
  exact ⟨s₁, s₂, j₁, j₂, hs₁0, hs₂0, hne, hj₁, hj₂, π, hπ⟩

/-- **Simon's problem**: `O(n)` quantum queries suffice, while `Ω(2 ^ (n / 2))` classical
queries are necessary. -/
theorem simon_algorithm (n : ℕ) (hn : 1 ≤ n) :
    (∀ s : Bits n, s ≠ 0 → ∃ Y : Finset (Bits n), Y.card ≤ n ∧
        (∀ y ∈ Y, dotp y s = 0) ∧
        ∀ t : Bits n, (∀ y ∈ Y, dotp y t = 0) → t = 0 ∨ t = s) ∧
    (∀ Q : Finset (Bits n),
        (∀ s : Bits n, s ≠ 0 → ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y ∧ y = x + s) → 2 ^ n ≤ Q.card ^ 2) ∧
    (∀ Q : Finset (Bits n), Q.card ^ 2 + 3 ≤ 2 ^ n →
        ∃ s₁ s₂ : Bits n, ∃ j₁ j₂ : Fin n, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧ s₁ ≠ s₂ ∧ s₁ j₁ = 1 ∧ s₂ j₂ = 1 ∧
          ∃ π : Bits n ≃ Bits n, ∀ x ∈ Q, π (simonFun s₁ j₁ x) = simonFun s₂ j₂ x) :=
  ⟨fun _ hs => simon_quantum_queries hs,
   fun Q hQ => simon_classical_lower_bound hn Q hQ,
   fun Q hQ => simon_classical_indistinguishable Q hQ⟩

end QI

#print axioms QI.simon_algorithm

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

