import Mathlib
namespace Brockian.Vandermonde
/-- Vandermonde's identity: ∑_k C(m,k)·C(n,p−k) = C(m+n, p). -/
theorem vandermonde (m n p : ℕ) :
    ∑ k ∈ Finset.range (p + 1), Nat.choose m k * Nat.choose n (p - k) = Nat.choose (m + n) p := by
  rw [Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => m.choose i * n.choose j)]
end Brockian.Vandermonde

