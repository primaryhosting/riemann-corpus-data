/-
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-- The cubic weight `psi`. -/
def psiCubic (m : ℕ) : ℚ :=
  (m : ℚ) / 2 + (2 * (m : ℚ) ^ 2 - (m : ℚ) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- Key factorization: for `m ≥ 2` the indicator vanishes and
`18 * (1 - psiCubic m) = (m - 2) * (m - 3) * (m + 3)`. -/
theorem eighteen_mul_one_sub_psiCubic {m : ℕ} (hm : 2 ≤ m) :
    18 * (1 - psiCubic m) = ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
  have h1 : m ≠ 1 := by omega
  simp only [psiCubic, h1, if_false]
  ring

/-- For an integer `m ≥ 2` we have `(m - 2) * (m - 3) ≥ 0` over `ℚ`. -/
theorem nonneg_mul_sub_two_sub_three {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
  rcases lt_or_ge m 4 with h | h
  · interval_cases m <;> norm_num
  · have h4 : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h
    nlinarith

/-- `psiCubic m ≤ 1` for every integer `m ≥ 1`. -/
theorem psiCubic_le_one : ∀ m : ℕ, 1 ≤ m → psiCubic m ≤ 1 := by
  intro m hm
  rcases eq_or_lt_of_le hm with h1 | h2
  · norm_num [psiCubic, ← h1]
  · have hm2 : 2 ≤ m := h2
    have key := eighteen_mul_one_sub_psiCubic hm2
    have hnn := nonneg_mul_sub_two_sub_three hm2
    have hpos : (0 : ℚ) < (m : ℚ) + 3 := by positivity
    nlinarith [mul_nonneg hnn (le_of_lt hpos)]

end Zeta23Scaffold

