/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 10·y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`), e.g. `(x, y) = (19, 6)`: `19² - 10 · 6² = 361 - 360 = 1`. -/
theorem pell_10 : ∃ x y : Int, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨19, 6, by decide, by decide⟩

end Math

