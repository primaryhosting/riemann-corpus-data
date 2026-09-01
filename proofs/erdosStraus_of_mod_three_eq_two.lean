import Mathlib

/-- `4 / n` is a sum of three unit fractions with positive denominators. -/
def ErdosStrausSolvable (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (4 : ℚ) / (n : ℚ) = 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ)

/-- The Erdős–Straus conjecture (**OPEN**), recorded as an unproven
`def`: every `n ≥ 2` admits such a representation. -/
def ErdosStrausConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n

/-- For `n ≡ 2 (mod 3)`, writing `n = 3k + 2`, the identity
`4/n = 1/n + 1/(k+1) + 1/(n(k+1))` gives an explicit representation. -/
theorem erdosStraus_of_mod_three_eq_two {n : ℕ} (hn : 2 ≤ n)
    (h : n % 3 = 2) : ErdosStrausSolvable n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨n, k + 1, n * (k + 1), by omega, by omega, by positivity, ?_⟩
  subst hk
  push_cast
  have h1 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

