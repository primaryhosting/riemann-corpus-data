import Mathlib
namespace Brockian.MsZeckendorf

open List Nat

local instance zeck_isTrans : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- A Zeckendorf representation, unfolded as a `Pairwise` statement on `l ++ [0]`. -/
lemma pairwise_of_isZeckendorfRep {l : List ℕ} (hl : l.IsZeckendorfRep) :
    (l ++ [0]).Pairwise (fun a b ↦ b + 2 ≤ a) := by
  rw [← List.isChain_iff_pairwise]
  exact hl

/-- In a strictly decreasing (by steps of at least `2`) list, no element is the successor of
another one. -/
lemma not_mem_succ_of_pairwise {l : List ℕ} (h : l.Pairwise (fun a b ↦ b + 2 ≤ a)) {i : ℕ}
    (hi : i ∈ l) (hj : i + 1 ∈ l) : False := by
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hi with rfl | hi'
    · rcases List.mem_cons.1 hj with hcon | hj'
      · omega
      · have := h.1 _ hj'; omega
    · rcases List.mem_cons.1 hj with rfl | hj'
      · have := h.1 _ hi'; omega
      · exact ih h.2 hi' hj'

/-- Every element of a Zeckendorf representation is at least `2`. -/
lemma two_le_of_mem_zeckendorf {l : List ℕ} (hl : l.IsZeckendorfRep) {i : ℕ} (hi : i ∈ l) :
    2 ≤ i := by
  have h := pairwise_of_isZeckendorfRep hl
  rw [List.pairwise_append] at h
  simpa using h.2.2 i hi 0 (by simp)

/-- A Zeckendorf representation has no duplicates. -/
lemma nodup_of_isZeckendorfRep {l : List ℕ} (hl : l.IsZeckendorfRep) : l.Nodup := by
  have h := pairwise_of_isZeckendorfRep hl
  rw [List.pairwise_append] at h
  exact h.1.imp (by omega)

/-- A Zeckendorf representation contains no two consecutive numbers. -/
lemma no_consecutive_of_isZeckendorfRep {l : List ℕ} (hl : l.IsZeckendorfRep) {i : ℕ}
    (hi : i ∈ l) : i + 1 ∉ l := by
  intro h
  have hp := pairwise_of_isZeckendorfRep hl
  rw [List.pairwise_append] at hp
  exact not_mem_succ_of_pairwise hp.1 hi h

/-- Zeckendorf's theorem (existence): every positive integer is a sum of non-consecutive
    Fibonacci numbers (indices ≥ 2, no two consecutive).

    (The positivity hypothesis `hn` is kept as stated, although the proof does not need it:
    the empty sum represents `0`.) -/
theorem zeckendorf_exists (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℕ, (∀ i ∈ S, 2 ≤ i) ∧ (∀ i ∈ S, i + 1 ∉ S) ∧
      ∑ i ∈ S, Nat.fib i = n := by
  classical
  obtain ⟨l, hl, hsum⟩ : ∃ l : List ℕ, l.IsZeckendorfRep ∧ (l.map Nat.fib).sum = n :=
    ⟨Nat.zeckendorf n, Nat.isZeckendorfRep_zeckendorf n, Nat.sum_zeckendorf_fib n⟩
  refine ⟨l.toFinset, ?_, ?_, ?_⟩
  · intro i hi
    exact two_le_of_mem_zeckendorf hl (List.mem_toFinset.1 hi)
  · intro i hi h
    exact no_consecutive_of_isZeckendorfRep hl (List.mem_toFinset.1 hi) (List.mem_toFinset.1 h)
  · rw [← hsum]
    exact List.sum_toFinset _ (nodup_of_isZeckendorfRep hl)

end Brockian.MsZeckendorf

