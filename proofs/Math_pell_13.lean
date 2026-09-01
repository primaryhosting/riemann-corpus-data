/-
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is kept verbatim; it is written as a plain block comment rather
-- than a `/-! ... -/` module docstring because Lean 4 requires `import` commands to
-- precede every other command in a file, including module docstrings.)

import Mathlib

namespace Math

/-- **Pell's equation for `d = 13`.**  The equation `x² - 13·y² = 1` has a
nontrivial integer solution, i.e. one with `y ≠ 0` (so `x ≠ ±1`).  The
fundamental solution is `(x, y) = (649, 180)`:
`649² - 13·180² = 421201 - 421200 = 1`. -/
theorem pell_13 : ∃ x y : ℤ, x ^ 2 - 13 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨649, 180, by norm_num, by norm_num⟩

end Math

