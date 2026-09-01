import Mathlib
namespace Brockian.MsBinet

private lemma sq_sqrt5 : Real.sqrt 5 ^ 2 = 5 := by
  rw [sq, Real.mul_self_sqrt (by norm_num)]

private lemma sqrt5_pos : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

private lemma phi_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = ((1 + Real.sqrt 5) / 2) + 1 := by
  have h := sq_sqrt5
  field_simp
  nlinarith [h]

private lemma psi_sq : ((1 - Real.sqrt 5) / 2) ^ 2 = ((1 - Real.sqrt 5) / 2) + 1 := by
  have h := sq_sqrt5
  field_simp
  nlinarith [h]

private lemma binet_aux (n : ℕ) :
    (Nat.fib n : ℝ) * Real.sqrt 5
        = ((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n
      ∧ (Nat.fib (n+1) : ℝ) * Real.sqrt 5
        = ((1 + Real.sqrt 5) / 2) ^ (n+1) - ((1 - Real.sqrt 5) / 2) ^ (n+1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      have hp : ((1 + Real.sqrt 5) / 2) ^ (k+2)
          = ((1 + Real.sqrt 5) / 2) ^ (k+1) + ((1 + Real.sqrt 5) / 2) ^ k := by
        have h := phi_sq
        calc ((1 + Real.sqrt 5) / 2) ^ (k+2)
            = ((1 + Real.sqrt 5) / 2) ^ k * ((1 + Real.sqrt 5) / 2) ^ 2 := by ring
          _ = ((1 + Real.sqrt 5) / 2) ^ k * (((1 + Real.sqrt 5) / 2) + 1) := by rw [h]
          _ = ((1 + Real.sqrt 5) / 2) ^ (k+1) + ((1 + Real.sqrt 5) / 2) ^ k := by ring
      have hq : ((1 - Real.sqrt 5) / 2) ^ (k+2)
          = ((1 - Real.sqrt 5) / 2) ^ (k+1) + ((1 - Real.sqrt 5) / 2) ^ k := by
        have h := psi_sq
        calc ((1 - Real.sqrt 5) / 2) ^ (k+2)
            = ((1 - Real.sqrt 5) / 2) ^ k * ((1 - Real.sqrt 5) / 2) ^ 2 := by ring
          _ = ((1 - Real.sqrt 5) / 2) ^ k * (((1 - Real.sqrt 5) / 2) + 1) := by rw [h]
          _ = ((1 - Real.sqrt 5) / 2) ^ (k+1) + ((1 - Real.sqrt 5) / 2) ^ k := by ring
      rw [hp, hq, Nat.fib_add_two]
      push_cast
      linarith [h0, h1]

/-- Binet's formula: Fₙ = (φⁿ − ψⁿ)/√5 with φ = (1+√5)/2, ψ = (1−√5)/2. -/
theorem binet (n : ℕ) :
    (Nat.fib n : ℝ)
      = (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) / Real.sqrt 5 := by
  rw [eq_div_iff (ne_of_gt sqrt5_pos)]
  exact (binet_aux n).1

end Brockian.MsBinet

