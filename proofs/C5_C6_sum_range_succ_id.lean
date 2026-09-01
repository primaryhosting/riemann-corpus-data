import Mathlib
open Finset
namespace C5.C6

/-- Gauss' summation formula, in the doubled form `2 * ∑_{i<n+1} i = n(n+1)`.
See `Finset.sum_range_id_mul_two` in Mathlib. -/
theorem sum_range_succ_id (n : ℕ) : 2 * ∑ i ∈ range (n+1), i = n*(n+1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- Every binomial coefficient `n.choose k` is at most `2 ^ n`
(`Nat.choose_le_two_pow` / sum of a row of Pascal's triangle). -/
theorem choose_le_pow (n k : ℕ) : n.choose k ≤ 2^n := by
  rcases le_or_gt k n with hk | hk
  · calc n.choose k ≤ ∑ i ∈ range (n+1), n.choose i :=
          Finset.single_le_sum (f := fun i => n.choose i) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      _ = 2 ^ n := Nat.sum_range_choose n
  · simp [Nat.choose_eq_zero_of_lt hk]

/-- Factorials are positive (`Nat.factorial_pos`). -/
theorem factorial_pos (n : ℕ) : 0 < n.factorial := Nat.factorial_pos n

end C5.C6

