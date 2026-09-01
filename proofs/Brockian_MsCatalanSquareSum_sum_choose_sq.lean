import Mathlib
namespace Brockian.MsCatalanSquareSum

open Finset

/-- The sum of squares of a row of Pascal's triangle: ∑_k C(n,k)² = C(2n,n). -/
theorem sum_choose_sq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 = Nat.choose (2 * n) n := by
  rw [two_mul, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hi), sq]

end Brockian.MsCatalanSquareSum

