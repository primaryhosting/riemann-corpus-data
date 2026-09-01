import Mathlib

/-!
# Erdős–Szekeres theorem

Any injective sequence of `r * s + 1` reals has a strictly increasing subsequence of length
`r + 1` or a strictly decreasing subsequence of length `s + 1`.

The proof is the classical pigeonhole argument: label each index `i` with the pair consisting of
the maximal length of an increasing subsequence ending at `i` and the maximal length of a
decreasing subsequence ending at `i`; these pairs are pairwise distinct, so if all increasing
sequences had length `≤ r` and all decreasing ones length `≤ s`, there would be at most `r * s`
indices.
-/

open Function Finset

namespace Brockian.ErdosSzekeres

section Aux

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β] {f : α → β} {i : α}

/-- The possible lengths of an increasing sequence which ends at `i`. -/
private noncomputable def incSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictMonoOn f t}

/-- The possible lengths of a decreasing sequence which ends at `i`. -/
private noncomputable def decSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictAntiOn f t}

/-- The singleton sequence is increasing, so 1 is a possible length. -/
private lemma one_mem_incSequencesTo : 1 ∈ incSequencesTo f i := mem_image.2 ⟨{i}, by simp⟩

/-- The singleton sequence is decreasing, so 1 is a possible length. -/
private lemma one_mem_decSequencesTo : 1 ∈ decSequencesTo f i := one_mem_incSequencesTo (β := βᵒᵈ)

private lemma incSequencesTo_nonempty : (incSequencesTo f i).Nonempty := ⟨1, one_mem_incSequencesTo⟩

private lemma decSequencesTo_nonempty : (decSequencesTo f i).Nonempty := ⟨1, one_mem_decSequencesTo⟩

/-- The maximum length of an increasing sequence which ends at `i`. -/
private noncomputable def maxIncSequencesTo (f : α → β) (i : α) : ℕ :=
  max' (incSequencesTo f i) incSequencesTo_nonempty

/-- The maximum length of a decreasing sequence which ends at `i`. -/
private noncomputable def maxDecSequencesTo (f : α → β) (i : α) : ℕ :=
  max' (decSequencesTo f i) decSequencesTo_nonempty

private lemma one_le_maxIncSequencesTo : 1 ≤ maxIncSequencesTo f i :=
  le_max' _ _ one_mem_incSequencesTo

private lemma one_le_maxDecSequencesTo : 1 ≤ maxDecSequencesTo f i :=
  le_max' _ _ one_mem_decSequencesTo

private lemma maxIncSequencesTo_mem : maxIncSequencesTo f i ∈ incSequencesTo f i :=
  max'_mem _ incSequencesTo_nonempty

private lemma maxDecSequencesTo_mem : maxDecSequencesTo f i ∈ decSequencesTo f i :=
  max'_mem _ decSequencesTo_nonempty

private lemma maxIncSequencesTo_lt {i j : α} (hij : i < j) (hfij : f i < f j) :
    maxIncSequencesTo f i < maxIncSequencesTo f j := by
  classical
  rw [Nat.lt_iff_add_one_le]
  refine le_max' _ _ ?_
  have : maxIncSequencesTo f i ∈ incSequencesTo f i := max'_mem _ incSequencesTo_nonempty
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc] at this
  obtain ⟨t, hti, ht₁, ht₂⟩ := this
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc]
  have hlt : ∀ x ∈ t, x < j := fun x hx ↦ (hti.2 hx).trans_lt hij
  refine ⟨insert j t, ?_, ?_, ?_⟩
  next =>
    convert hti.insert j using 1
    next => simp
    next => rw [max_eq_left hij.le]
  next =>
    simp only [coe_insert]
    rw [strictMonoOn_insert_iff_of_forall_le]
    · refine ⟨?_, ht₁⟩
      intro x hx hxj
      exact (ht₁.monotoneOn hx hti.1 (hti.2 hx)).trans_lt hfij
    · exact fun x hx ↦ (hlt x hx).le
  have hj : j ∉ t := fun hj ↦ lt_irrefl _ (hlt _ hj)
  simp [hj, ht₂]

private lemma maxDecSequencesTo_gt {i j : α} (hij : i < j) (hfij : f j < f i) :
    maxDecSequencesTo f i < maxDecSequencesTo f j :=
  maxIncSequencesTo_lt (β := βᵒᵈ) hij hfij

/-- The pair of labels attached to an index. -/
private noncomputable def paired (f : α → β) (i : α) : ℕ × ℕ :=
  (maxIncSequencesTo f i, maxDecSequencesTo f i)

private lemma paired_injective (hf : Injective f) : Injective (paired f) := by
  apply Injective.of_lt_imp_ne
  intro i j hij q
  cases lt_or_gt_of_ne (hf.ne hij.ne)
  case inl h => exact (maxIncSequencesTo_lt hij h).ne congr($q.1)
  case inr h => exact (maxDecSequencesTo_gt hij h).ne congr($q.2)

/-- **Erdős–Szekeres Theorem** (general form): given an injective sequence of more than `r * s`
values, there is an increasing subsequence of length longer than `r` or a decreasing one of
length longer than `s`. -/
private theorem erdos_szekeres_aux {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α)
    (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := by
  classical
  rsuffices ⟨i, hi⟩ : ∃ i, r < maxIncSequencesTo f i ∨ s < maxDecSequencesTo f i
  · refine Or.imp ?_ ?_ hi
    on_goal 1 =>
      have : maxIncSequencesTo f i ∈ image card _ := maxIncSequencesTo_mem
    on_goal 2 =>
      have : maxDecSequencesTo f i ∈ image card _ := maxDecSequencesTo_mem
    all_goals
      intro hi
      obtain ⟨t, ht₁, ht₂⟩ := mem_image.1 this
      refine ⟨t, by rwa [ht₂], ?_⟩
      rw [mem_filter] at ht₁
      exact ht₁.2.2
  by_contra! q
  have : Set.MapsTo (paired f) (univ : Finset α) (Icc 1 r ×ˢ Icc 1 s : Finset _) := by
    simp [paired, one_le_maxIncSequencesTo, one_le_maxDecSequencesTo, Set.MapsTo, *]
  refine hn.not_ge ?_
  simpa using card_le_card_of_injOn (paired f) this (paired_injective hf).injOn

end Aux

/-- Erdős–Szekeres: any sequence of r·s+1 distinct reals has a monotone subsequence of length
    r+1 (increasing) or s+1 (decreasing). -/
theorem erdos_szekeres (r s : ℕ) (f : Fin (r * s + 1) → ℝ) (hf : Function.Injective f) :
    (∃ t : Finset (Fin (r * s + 1)), t.card = r + 1 ∧
        StrictMonoOn f ↑t) ∨
    (∃ t : Finset (Fin (r * s + 1)), t.card = s + 1 ∧
        StrictAntiOn f ↑t) := by
  have hn : r * s < Fintype.card (Fin (r * s + 1)) := by simp
  rcases erdos_szekeres_aux hn hf with ⟨t, ht, hmono⟩ | ⟨t, ht, hanti⟩
  · obtain ⟨t', ht's, ht'card⟩ := Finset.exists_subset_card_eq (show r + 1 ≤ #t from ht)
    exact Or.inl ⟨t', ht'card, hmono.mono (by exact_mod_cast Finset.coe_subset.2 ht's)⟩
  · obtain ⟨t', ht's, ht'card⟩ := Finset.exists_subset_card_eq (show s + 1 ≤ #t from ht)
    exact Or.inr ⟨t', ht'card, hanti.mono (by exact_mod_cast Finset.coe_subset.2 ht's)⟩

end Brockian.ErdosSzekeres

