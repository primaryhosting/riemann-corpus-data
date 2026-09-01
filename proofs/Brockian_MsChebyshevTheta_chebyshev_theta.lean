import Mathlib
namespace Brockian.MsChebyshevTheta
/-- Chebyshev's upper bound: the first Chebyshev function θ(n) = ∑_{p ≤ n} log p satisfies
    θ(n) ≤ n·log 4. -/
theorem chebyshev_theta (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ≤ n * Real.log 4 := by
  -- The sum of `log p` over primes `p ≤ n` is the logarithm of the primorial `n#`.
  have h1 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p
      = Real.log (primorial n) := by
    unfold primorial
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      exact_mod_cast (Finset.mem_filter.mp hp).2.pos.ne')]
  rw [h1]
  calc Real.log (primorial n) ≤ Real.log ((4 : ℕ) ^ n) := by
        apply Real.log_le_log <;> norm_cast
        exacts [primorial_pos _, primorial_le_4_pow _]
    _ = n * Real.log 4 := by
        push_cast
        rw [Real.log_pow]
end Brockian.MsChebyshevTheta

