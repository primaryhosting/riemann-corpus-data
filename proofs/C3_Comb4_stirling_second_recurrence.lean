import Mathlib
open Finset
namespace C3.Comb4

/-- The original statement is a vacuous implication into `True`, so it holds trivially.
(Note that its hypothesis, Pascal's rule in the form
`(n+1).choose k = n.choose k + n.choose (k-1)`, is false for `k = 0`, where truncated
subtraction gives `n.choose 0 + n.choose 0 = 2 ≠ 1`; see `pascal_rule` below for the
corrected, unconditional form.) -/
theorem stirling_second_recurrence (n k : ℕ) :
    (n+1).choose k = n.choose k + n.choose (k-1) → True := fun _ => trivial

/-- Pascal's rule, stated for `0 < k` (the hypothesis needed to make the
`k - 1` truncated subtraction meaningful). -/
theorem pascal_rule (n k : ℕ) (hk : 0 < k) :
    (n+1).choose k = n.choose k + n.choose (k-1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp [Nat.choose_succ_succ, Nat.add_comm]

theorem sum_choose_row (n : ℕ) : ∑ k ∈ range (n+1), n.choose k = 2^n :=
  Nat.sum_range_choose n

theorem alternating_choose (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range (n+1), (-1:ℤ)^k * n.choose k = 0 :=
  Int.alternating_sum_range_choose_of_ne hn.ne'

end C3.Comb4

