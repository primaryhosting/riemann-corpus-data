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
    rw [Nat.factorization_def n hp]
    by_cases hpn : p ∣ n
    · exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩) hp4
    · rw [padicValNat.eq_zero_of_not_dvd hpn]
      exact Even.zero
  · intro h p hp hp4
    have h' := h p (Nat.prime_of_mem_primeFactors hp) hp4
    rwa [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)] at h'
end Brockian.TwoSquares

