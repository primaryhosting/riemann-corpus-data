import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
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

set_option grind.warning false

namespace Math

section Mirsky

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains of a finite partial order. -/
noncomputable def chainsOf (α : Type*) [Fintype α] [PartialOrder α] : Finset (Finset α) :=
  Finset.univ.filter (fun C : Finset α => IsChain (· ≤ ·) (↑C : Set α))

lemma mem_chainsOf {C : Finset α} : C ∈ chainsOf α ↔ IsChain (· ≤ ·) (↑C : Set α) := by
  simp [chainsOf]

/-- The largest cardinality of a chain. -/
noncomputable def maxChainCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (chainsOf α).sup Finset.card

/-- The height of an element: the largest cardinality of a chain all of whose elements are
below (or equal to) it. -/
noncomputable def height (x : α) : ℕ :=
  ((chainsOf α).filter (fun C => ∀ y ∈ C, y ≤ x)).sup Finset.card

lemma chainsOf_nonempty : (chainsOf α).Nonempty :=
  ⟨∅, by simp [mem_chainsOf]⟩

lemma card_le_maxChainCard {C : Finset α} (hC : IsChain (· ≤ ·) (↑C : Set α)) :
    C.card ≤ maxChainCard α :=
  Finset.le_sup (f := Finset.card) (mem_chainsOf.2 hC)

lemma exists_chain_card_eq_maxChainCard :
    ∃ C : Finset α, IsChain (· ≤ ·) (↑C : Set α) ∧ C.card = maxChainCard α := by
  obtain ⟨C, hC, hcard⟩ :=
    Finset.exists_mem_eq_sup (chainsOf α) chainsOf_nonempty Finset.card
  exact ⟨C, mem_chainsOf.1 hC, hcard.symm⟩

lemma exists_chain_height (x : α) :
    ∃ C : Finset α, IsChain (· ≤ ·) (↑C : Set α) ∧ (∀ y ∈ C, y ≤ x) ∧ C.card = height x := by
  have hne : ((chainsOf α).filter (fun C => ∀ y ∈ C, y ≤ x)).Nonempty := by
    refine ⟨{x}, ?_⟩
    simp [Finset.mem_filter, mem_chainsOf]
  obtain ⟨C, hC, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter] at hC
  exact ⟨C, mem_chainsOf.1 hC.1, hC.2, hcard.symm⟩

lemma one_le_height (x : α) : 1 ≤ height x := by
  have : ({x} : Finset α) ∈ (chainsOf α).filter (fun C => ∀ y ∈ C, y ≤ x) := by
    simp [Finset.mem_filter, mem_chainsOf]
  simpa using Finset.le_sup (f := Finset.card) this

lemma height_le_maxChainCard (x : α) : height x ≤ maxChainCard α := by
  obtain ⟨C, hC, -, hcard⟩ := exists_chain_height x
  exact hcard ▸ card_le_maxChainCard hC

lemma height_strictMono {x y : α} (hxy : x < y) : height x < height y := by
  obtain ⟨C, hC, hCx, hcard⟩ := exists_chain_height x
  have hy : y ∉ C := fun hy => absurd (hCx y hy) (not_le_of_gt hxy)
  have hchain : IsChain (· ≤ ·) (↑(insert y C) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr (le_trans (le_trans (hCx b hb) hxy.le) le_rfl)
    · rcases hb with rfl | hb
      · exact Or.inl (le_trans (hCx a ha) hxy.le)
      · exact hC ha hb hab
  have hmem : insert y C ∈ (chainsOf α).filter (fun C => ∀ z ∈ C, z ≤ y) := by
    refine Finset.mem_filter.2 ⟨mem_chainsOf.2 hchain, ?_⟩
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact le_rfl
    · exact le_trans (hCx z hz) hxy.le
  have := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hy, hcard] at this
  exact this

end Mirsky

/-- **Mirsky's theorem** (the "dual Dilworth" theorem): in a finite partial order, the minimum
number of antichains needed to cover the order equals the maximum cardinality of a chain.

Antichain covers by `n` antichains are encoded as colourings `A : α → ℕ` taking values `< n`,
each colour class being an antichain (i.e. any two comparable elements of the same colour are
equal). -/
theorem dilworth {α : Type*} [Fintype α] [PartialOrder α] :
    ∃ k : ℕ,
      IsGreatest {n : ℕ | ∃ C : Finset α, IsChain (· ≤ ·) (↑C : Set α) ∧ C.card = n} k ∧
      IsLeast {n : ℕ | ∃ A : α → ℕ, (∀ a : α, A a < n) ∧
        ∀ x y : α, A x = A y → x ≤ y → x = y} k := by
  refine ⟨maxChainCard α, ⟨exists_chain_card_eq_maxChainCard, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro n ⟨C, hC, rfl⟩
    exact card_le_maxChainCard hC
  · -- the height function is a valid colouring with `maxChainCard α` colours
    refine ⟨fun x => height x - 1, fun a => ?_, ?_⟩
    · have h1 := one_le_height a
      have h2 := height_le_maxChainCard a
      omega
    · intro x y hxy hle
      by_contra hne
      have hlt : x < y := lt_of_le_of_ne hle hne
      have := height_strictMono hlt
      have h1 := one_le_height x
      omega
  · rintro n ⟨A, hA, hAc⟩
    obtain ⟨C, hC, hcard⟩ := exists_chain_card_eq_maxChainCard (α := α)
    rw [← hcard]
    have : C.card ≤ (Finset.range n).card := by
      refine Finset.card_le_card_of_injOn A (fun a ha => Finset.mem_range.2 (hA a)) ?_
      intro a ha b hb hab
      rcases eq_or_ne a b with rfl | hne
      · rfl
      · rcases hC (by simpa using ha) (by simpa using hb) hne with h | h
        · exact hAc a b hab h
        · exact (hAc b a hab.symm h).symm
    simpa using this

end Math

