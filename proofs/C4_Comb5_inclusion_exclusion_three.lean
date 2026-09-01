import Mathlib
open Finset
namespace C4.Comb5

theorem inclusion_exclusion_three {α : Type*} [DecidableEq α] (A B C : Finset α) :
    (A ∪ B ∪ C).card = A.card + B.card + C.card - (A∩B).card - (A∩C).card - (B∩C).card + (A∩B∩C).card := by
  have hAB : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hABC : ((A ∪ B) ∪ C).card + ((A ∪ B) ∩ C).card = (A ∪ B).card + C.card :=
    Finset.card_union_add_card_inter (A ∪ B) C
  have hdist : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have hmid : ((A ∩ C) ∪ (B ∩ C)).card + ((A ∩ C) ∩ (B ∩ C)).card
      = (A ∩ C).card + (B ∩ C).card :=
    Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have hcap : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x; simp only [Finset.mem_inter]; tauto
  have hsub : (A ∩ B ∩ C).card ≤ (A ∪ B ∪ C).card := by
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_union] at *
    tauto
  rw [hcap] at hmid
  rw [hdist] at hABC
  omega

theorem pascal (n k : ℕ) : (n+1).choose (k+1) = n.choose k + n.choose (k+1) :=
  Nat.choose_succ_succ n k

theorem catalan_le (n : ℕ) : catalan n ≤ 4^n := by
  have h : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
  have hb : n.centralBinom ≤ 4 ^ n := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    calc (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  calc catalan n ≤ (n + 1) * catalan n := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    _ = n.centralBinom := h
    _ ≤ 4 ^ n := hb

end C4.Comb5

