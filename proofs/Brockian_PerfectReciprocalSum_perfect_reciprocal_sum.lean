import Mathlib
namespace Brockian.PerfectReciprocalSum
/-- The sum of the reciprocals of the divisors of a perfect number equals 2
    (since σ(n) = 2n). -/
theorem perfect_reciprocal_sum (n : ℕ) (hn : 0 < n) (hp : Nat.Perfect n) :
    ∑ d ∈ n.divisors, (1 / (d : ℚ)) = 2 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hsigma : ∑ d ∈ n.divisors, d = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hn).mp hp
  calc
    ∑ d ∈ n.divisors, (1 / (d : ℚ)) =
        ∑ d ∈ n.divisors, ((n / d : ℕ) : ℚ) / n := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
          have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
          rw [eq_div_iff hnq]
          field_simp
          exact_mod_cast (show n = d * (n / d) by
            simpa [mul_comm] using (Nat.div_mul_cancel hdvd).symm)
    _ = (∑ d ∈ n.divisors, ((n / d : ℕ) : ℚ)) / n := by
          rw [Finset.sum_div]
    _ = (∑ d ∈ n.divisors, (d : ℚ)) / n := by
          rw [Nat.sum_div_divisors]
    _ = ((∑ d ∈ n.divisors, d : ℕ) : ℚ) / n := by
          push_cast
          rfl
    _ = ((2 * n : ℕ) : ℚ) / n := by rw [hsigma]
    _ = 2 := by
          apply (div_eq_iff hnq).2
          norm_num
end Brockian.PerfectReciprocalSum

