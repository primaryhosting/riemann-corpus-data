import Mathlib
open Finset
namespace C6.C7

/-- `6 * ∑_{i=0}^{n} i^2 = n(n+1)(2n+1)`, by induction on `n`. -/
theorem sum_sq_formula (n : ℕ) : 6 * ∑ i ∈ range (n+1), i^2 = n*(n+1)*(2*n+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

/-- `C(n,k) * k! * (n-k)! = n!` for `k ≤ n`
(`Nat.choose_mul_factorial_mul_factorial` in Mathlib). -/
theorem choose_mul (n k : ℕ) (h : k ≤ n) :
    n.choose k * k.factorial * (n-k).factorial = n.factorial :=
  Nat.choose_mul_factorial_mul_factorial h

/-- The sum of the squares of a row of Pascal's triangle is a central binomial
coefficient (`Nat.sum_range_choose_sq`, a consequence of Vandermonde's identity). -/
theorem sum_choose_two (n : ℕ) : ∑ k ∈ range (n+1), (n.choose k)^2 = (2*n).choose n :=
  Nat.sum_range_choose_sq n

end C6.C7

