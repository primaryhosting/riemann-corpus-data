import Mathlib
namespace Brockian.MsMirsky

/-!
# Mirsky's theorem (dual Dilworth)

The original statement in this file asked for a family `A : Finset (Finset α)` of antichains
with `A.card = n` exactly.  That is not provable: a `Finset (Finset α)` consists of *distinct*
antichains, and there simply may not be `n` of them.  For instance with `α = Unit` and `n = 5`
the chain hypothesis holds (every chain has at most one element), yet
`Fintype.card (Finset (Finset Unit)) = 4 < 5`, so no `A` of cardinality `5` exists at all.

The statement below is therefore the standard form of Mirsky's theorem: the poset is covered by
*at most* `n` antichains (`A.card ≤ n`).  The mathematical content — "if all chains have size
at most `n`, then the poset is a union of `n` antichains" — is unchanged.  The original, false,
statement is kept commented out at the end of the file.

The proof uses the height function `height x`, the maximal cardinality of a chain contained in
`{y | y ≤ x}`; the level sets of `height` are antichains, and there are at most `n` of them.
-/

open Classical in
/-- The *height* of `x`: the maximal cardinality of a chain all of whose elements are `≤ x`. -/
noncomputable def height {α : Type*} [Fintype α] [PartialOrder α] (x : α) : ℕ :=
  (Finset.univ.filter
      (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x)).sup Finset.card

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- The set of chains below `x`, over which the height is a supremum, is nonempty. -/
lemma height_filter_nonempty (x : α) :
    (Finset.univ.filter
      (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x)).Nonempty := by
  use ∅
  simp [IsChain]

/-- The height of `x` is realised by an actual chain below `x`. -/
lemma exists_chain_height (x : α) :
    ∃ c : Finset α, IsChain (· ≤ ·) (c : Set α) ∧ (∀ y ∈ c, y ≤ x) ∧ c.card = height x := by
  open Classical in
  set S := Finset.univ.filter (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x) with hS
  have hne : S.Nonempty := height_filter_nonempty x
  unfold height
  let S' := S.image Finset.card
  have hne' : S'.Nonempty := ⟨_, Finset.mem_image_of_mem _ (hne.choose_spec)⟩
  let m := S'.max' hne'
  have hm_in_S' : m ∈ S' := Finset.max'_mem S' hne'
  obtain ⟨c, hc_mem, hc_card⟩ := Finset.mem_image.mp hm_in_S'
  use c
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hc_mem ⊢
  refine ⟨hc_mem.1, hc_mem.2, ?_⟩
  rw [hc_card]
  unfold m S'
  rw [Finset.max'_eq_sup', Finset.sup'_eq_sup hne', Finset.sup_image]
  rfl

/-- Every element has positive height, witnessed by the singleton chain `{x}`. -/
lemma one_le_height (x : α) : 1 ≤ height x := by
  simp only [height]
  refine Finset.le_sup (f := Finset.card) (b := {x}) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · have : IsChain (· ≤ ·) (({x} : Finset α) : Set α) := by simp [IsChain]
    exact this
  · intro y hy
    simp at hy
    exact hy ▸ le_rfl

/-- The height is monotone-strict along the strict order. -/
lemma height_lt_height {x y : α} (h : x < y) : height x < height y := by
  open Classical in
  obtain ⟨c, hc_chain, hc_le, hc_card⟩ := exists_chain_height x
  have hc_lt_y : ∀ z ∈ c, z < y := fun z hz => lt_of_le_of_lt (hc_le z hz) h
  -- Show y ∉ c (otherwise y ≤ x, contradicting x < y)
  have hy_notin_c : y ∉ c := fun hy => h.not_ge (hc_le y hy)
  -- Define c' = c ∪ {y}
  let c' : Finset α := {y} ∪ c
  have hc'_chain : IsChain (· ≤ ·) (c' : Set α) := by
    have hc'_coe : (c' : Set α) = ({y} : Set α) ∪ (c : Set α) := by simp [c']
    rw [hc'_coe]
    intro a ha b hb hab
    simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | hac
    · rcases hb with rfl | hbc
      · exact absurd rfl hab
      · exact Or.inr (le_of_lt (hc_lt_y b hbc))
    · rcases hb with rfl | hbc
      · exact Or.inl (le_of_lt (hc_lt_y a hac))
      · exact hc_chain hac hbc hab
  have hc'_le : ∀ z ∈ c', z ≤ y := by
    intro z hz
    rw [Finset.mem_union, Finset.mem_singleton] at hz
    cases hz with
    | inl hz => exact hz ▸ le_refl y
    | inr hz => exact le_trans (hc_le z hz) (le_of_lt h)
  have hc'_card : c'.card = c.card + 1 := by
    show ({y} ∪ c).card = c.card + 1
    rw [Finset.card_union_of_disjoint (by simpa using hy_notin_c), Finset.card_singleton,
      Nat.add_comm]
  -- height y ≥ c'.card = c.card + 1 = height x + 1 > height x
  calc height x = c.card := hc_card.symm
    _ < c.card + 1 := Nat.lt_succ_self _
    _ = c'.card := hc'_card.symm
    _ ≤ height y := by
        apply Finset.le_sup (f := Finset.card) (hb := _)
        simp [hc'_chain]
        exact hc'_le

/-- If all chains have at most `n` elements, all heights are at most `n`. -/
lemma height_le_of_chain_le {n : ℕ}
    (hchain : ∀ c : Finset α, IsChain (· ≤ ·) (c : Set α) → c.card ≤ n) (x : α) :
    height x ≤ n := by
  unfold height
  apply Finset.sup_le
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact hchain c hc.1

/-- Each level set of the height function is an antichain. -/
lemma isAntichain_height_level [DecidableEq α] (k : ℕ) :
    IsAntichain (· ≤ ·) ((Finset.univ.filter (fun x : α => height x = k) : Finset α) : Set α) := by
  intro a ha b hb hab hle
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hlt : a < b := hab.lt_of_le hle
  linarith [height_lt_height hlt]

/-- **Mirsky's theorem** (dual of Dilworth): if every chain in a finite poset has size `≤ n`,
    then the poset can be covered by (at most) `n` antichains. -/
theorem mirsky {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α] (n : ℕ)
    (hchain : ∀ c : Finset α, IsChain (· ≤ ·) (c : Set α) → c.card ≤ n) :
    ∃ A : Finset (Finset α), A.card ≤ n ∧
      (∀ a ∈ A, IsAntichain (· ≤ ·) (a : Set α)) ∧ (∀ x : α, ∃ a ∈ A, x ∈ a) := by
  refine ⟨(Finset.Icc 1 n).image (fun k => Finset.univ.filter (fun x : α => height x = k)),
    ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · rintro a ha
    simp only [Finset.mem_image] at ha
    obtain ⟨k, -, rfl⟩ := ha
    exact isAntichain_height_level k
  · intro x
    refine ⟨Finset.univ.filter (fun y : α => height y = height x), ?_, by simp⟩
    exact Finset.mem_image_of_mem _
      (Finset.mem_Icc.2 ⟨one_le_height x, height_le_of_chain_le hchain x⟩)

/- The original statement of the theorem, which is false as explained above:

theorem mirsky' {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α] (n : ℕ)
    (hchain : ∀ c : Finset α, IsChain (· ≤ ·) (c : Set α) → c.card ≤ n) :
    ∃ A : Finset (Finset α), A.card = n ∧
      (∀ a ∈ A, IsAntichain (· ≤ ·) (a : Set α)) ∧ (∀ x : α, ∃ a ∈ A, x ∈ a)
-/

end Brockian.MsMirsky

