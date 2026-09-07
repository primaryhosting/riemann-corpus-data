import Mathlib
namespace Brockian.MersenneExponentPrime
/-- If 2^n - 1 is prime then n is prime. Prove; axiom-clean, no sorry. -/
theorem mersenne_exponent_prime {n : ℕ} (h : (2 ^ n - 1).Prime) : n.Prime := by
  have hn : n ≠ 1 := by
    intro hn
    subst n
    norm_num at h
  exact (Nat.prime_of_pow_sub_one_prime hn h).2
end Brockian.MersenneExponentPrime
