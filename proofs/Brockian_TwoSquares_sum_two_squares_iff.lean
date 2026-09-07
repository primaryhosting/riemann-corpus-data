import Mathlib
namespace Brockian.TwoSquares
/-- Sum of two squares: n>0 is a² + b² iff every prime ≡ 3 (mod 4) in its factorization
    occurs to an even power. -/
theorem sum_two_squares_iff (n : ℕ) (hn : 0 < n) :
    (∃ a b : ℕ, n = a ^ 2 + b ^ 2) ↔
      ∀ p, p.Prime → p % 4 = 3 → Even (n.factorization p) := by
  rw [Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hp4
    by_cases hpd : p ∣ n
    · have hmem : p ∈ n.primeFactors :=
        hp.mem_primeFactors hpd (Nat.ne_of_gt hn)
      simpa [Nat.factorization_def n hp] using h p hmem hp4
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      exact Even.zero
  · intro h p hmem hp4
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
    simpa [Nat.factorization_def n hp] using h p hp hp4
end Brockian.TwoSquares
