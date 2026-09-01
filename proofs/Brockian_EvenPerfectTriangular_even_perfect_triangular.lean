import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

namespace Brockian.EvenPerfectTriangular

open Nat

/-- Every even perfect number is a triangular number: `n = k(k+1)/2` for some `k`.

The Euclid–Euler theorem writes `n` as `2^r * (2^(r+1) - 1)`.  Taking the
Mersenne number `2^(r+1) - 1` as the triangular index gives the result. -/
theorem even_perfect_triangular {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    ∃ k : ℕ, n = k * (k + 1) / 2 := by
  obtain ⟨r, -, rfl⟩ :=
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect he hp
  refine ⟨mersenne (r + 1), ?_⟩
  rw [mersenne]
  have hpos : 0 < 2 ^ (r + 1) := by positivity
  rw [Nat.sub_add_cancel hpos]
  rw [pow_succ]
  simp [Nat.mul_div_assoc]
  ac_rfl

end Brockian.EvenPerfectTriangular

