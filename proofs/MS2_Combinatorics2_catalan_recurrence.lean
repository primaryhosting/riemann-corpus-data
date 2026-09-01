import Mathlib
open Finset
namespace MS2.Combinatorics2

/-- Segner's recurrence for the Catalan numbers, stated as a sum over `range (n+1)`. -/
theorem catalan_recurrence (n : ℕ) : (catalan (n+1)) = ∑ i ∈ range (n+1), catalan i * catalan (n-i) := by
  rw [catalan_succ, Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (n - i))]

/-- As stated, this is an implication whose conclusion is `True`, hence trivially provable.
The genuine derangement formula is proved below as `derangement_formula'`. -/
theorem derangement_formula (n : ℕ) : (Nat.factorial n : ℤ) * (∑ k ∈ range (n+1), (-1)^k / (Nat.factorial k : ℤ)) = 0 → True :=
  fun _ => trivial

/-- The derangement formula: `D n = n! * ∑_{k=0}^{n} (-1)^k / k!`, over `ℚ` (over `ℤ` the
division inside the sum would be truncated integer division). -/
theorem derangement_formula' (n : ℕ) :
    (numDerangements n : ℚ)
      = (Nat.factorial n : ℚ) * ∑ k ∈ range (n+1), (-1:ℚ)^k / (Nat.factorial k : ℚ) := by
  have h := numDerangements_sum n
  have h2 : (numDerangements n : ℚ)
      = ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * Nat.ascFactorial (k + 1) (n - k) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hf : (Nat.factorial k) * Nat.ascFactorial (k+1) (n - k) = Nat.factorial n := by
    rw [Nat.factorial_mul_ascFactorial]
    congr 1
    omega
  have hk0 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  field_simp
  rw [← hf]
  push_cast
  ring

/-- The binomial theorem over `ℝ`. -/
theorem binomial_theorem (x y : ℝ) (n : ℕ) : (x+y)^n = ∑ k ∈ range (n+1), (n.choose k) * x^k * y^(n-k) := by
  rw [add_pow]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Vandermonde's identity. -/
theorem vandermonde_id (m n r : ℕ) : (m+n).choose r = ∑ k ∈ range (r+1), m.choose k * n.choose (r-k) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- As stated, this is an implication whose conclusion is `True`, hence trivially provable.
(A faithful formalization of Cayley's formula — the number of labelled trees on `n` vertices
is `n^(n-2)` — is not available in Mathlib and is not proved here.) -/
theorem cayley_formula (n : ℕ) (hn : 0 < n) : Fintype.card {t : SimpleGraph (Fin n) // t.IsTree} = n^(n-2) → True :=
  fun _ => trivial

end MS2.Combinatorics2

