/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`.
(By convention `rad 0 = rad 1 = 1`, the empty product.) -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The set of `abc`-exceptional triples for a given `ε`: triples of positive
coprime naturals with `a + b = c` and `rad (a*b*c) ^ (1+ε) < c`. -/
def abcExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
    ((rad (t.1 * t.2.1 * t.2.2) : ℝ)) ^ (1 + ε) < (t.2.2 : ℝ)}

/-- **The abc conjecture**: for every `ε > 0` there are only finitely many
coprime triples `a + b = c` of positive integers with `c > rad(abc)^(1+ε)`. -/
def AbcConjecture : Prop := ∀ ε : ℝ, 0 < ε → (abcExceptions ε).Finite

/-- The radical is always at least `1`. -/
theorem one_le_rad (n : ℕ) : 1 ≤ rad n := by
  rw [rad]
  exact Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).pos.ne'

/-- Exceptional sets are antitone in `ε`: a smaller exponent yields a larger set. -/
theorem abcExceptions_subset {ε ε' : ℝ} (h : ε ≤ ε') :
    abcExceptions ε' ⊆ abcExceptions ε := by
  rintro ⟨a, b, c⟩ ⟨ha, hb, hcop, hsum, hlt⟩
  refine ⟨ha, hb, hcop, hsum, lt_of_le_of_lt ?_ hlt⟩
  have h1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := by
    exact_mod_cast one_le_rad (a * b * c)
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- A concrete exceptional triple for the (false) exponent `ε = 0`:
`1 + 8 = 9` while `rad (1 * 8 * 9) = 6 < 9`. -/
theorem one_eight_nine_mem_abcExceptions_zero : ((1 : ℕ), (8 : ℕ), (9 : ℕ)) ∈ abcExceptions 0 := by
  refine ⟨one_pos, by norm_num, by decide, by norm_num, ?_⟩
  have : rad (1 * 8 * 9) = 6 := by
    simp [rad, show (1 * 8 * 9 : ℕ) = 72 from rfl, Nat.primeFactors]
  rw [this]
  norm_num

/-- **Main statement / Lean-checked reduction.**  The abc conjecture (quantified over all
real `ε > 0`) is equivalent to its countable restriction to the exponents `ε = 1/n`
for positive naturals `n`. -/
theorem abc_statement :
    AbcConjecture ↔ ∀ n : ℕ, 0 < n → (abcExceptions (1 / (n : ℝ))).Finite := by
  constructor
  · intro h n hn
    exact h _ (by positivity)
  · intro h ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    have hnpos : 0 < n := by
      by_contra hc
      push_neg at hc
      interval_cases n
      · simp at hn
        exact absurd hn (not_lt.mpr (by positivity))
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hle : 1 / (n : ℝ) ≤ ε := by
      rw [div_le_iff₀ hnR]
      rw [div_lt_iff₀ hε] at hn
      linarith
    exact (h n hnpos).subset (abcExceptions_subset hle)

end Frontier

