import Mathlib

def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n + 1

/-- No prime is quasiperfect: for a prime `p`, `sigma1 p = 1 + p < 2 * p + 1`. -/
theorem not_quasiperfect_prime {p : ℕ} (hp : Nat.Prime p) :
    ¬ Quasiperfect p := by
  rintro ⟨hpos, hsum⟩
  rw [sigma1, hp.divisors, Finset.sum_pair hp.one_lt.ne] at hsum
  omega

#print axioms not_quasiperfect_prime

