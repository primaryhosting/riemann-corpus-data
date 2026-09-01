import Mathlib
namespace Brockian.Nicomachus
/-- Nicomachus's theorem: the square of the n-th triangular number equals the sum of the first n cubes. -/
theorem sq_sum_eq_sum_cubes (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k) ^ 2 = ∑ k ∈ Finset.range (n + 1), k ^ 3 := by
  -- Gauss's formula for the triangular numbers, proved inline.
  have gauss : ∀ m : ℕ, 2 * ∑ k ∈ Finset.range (m + 1), k = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := gauss n
    have h2 := gauss (n + 1)
    rw [Finset.sum_range_succ (f := fun k => k ^ 3), ← ih]
    have key : 4 * (∑ k ∈ Finset.range (n + 1 + 1), k) ^ 2
        = 4 * ((∑ k ∈ Finset.range (n + 1), k) ^ 2 + (n + 1) ^ 3) := by
      have e1 : (2 * ∑ k ∈ Finset.range (n + 1 + 1), k) ^ 2 = ((n + 1) * (n + 1 + 1)) ^ 2 := by
        rw [h2]
      have e2 : (2 * ∑ k ∈ Finset.range (n + 1), k) ^ 2 = (n * (n + 1)) ^ 2 := by rw [h1]
      ring_nf at e1 e2 ⊢
      nlinarith [e1, e2]
    omega
end Brockian.Nicomachus

