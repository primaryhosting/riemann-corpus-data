/-
# M 2 At One Assembly
Category: C Integral
Target: Zeta23Scaffold.m2_at_one_assembly
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The (normalized) sine kernel `S u = sin (π u) / (π u)`. -/
noncomputable def S (u : ℝ) : ℝ := Real.sin (Real.pi * u) / (Real.pi * u)

/--
Conditional assembly of the second moment at one:
`m₂(1) = 1 + ∫ S² - ∫ S⁴ = 4/3`,
given the two sinc integrals as explicit hypotheses.
-/
theorem m2_at_one_assembly
    (hS2 : ∫ u : ℝ, (S u) ^ 2 = 1)
    (hS4 : ∫ u : ℝ, (S u) ^ 4 = 2 / 3) :
    1 + ((∫ u : ℝ, (S u) ^ 2) - (∫ u : ℝ, (S u) ^ 4)) = 4 / 3 := by
  rw [hS2, hS4]
  norm_num

end Zeta23Scaffold

