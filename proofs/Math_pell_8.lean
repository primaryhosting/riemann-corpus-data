/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 8`.**

The equation `x² - 8·y² = 1` has a nontrivial integer solution, i.e. a solution
with `y ≠ 0` (so `(x, y)` is not one of the trivial solutions `(±1, 0)`).

Witness: `(x, y) = (3, 1)`, since `3² - 8·1² = 9 - 8 = 1`. -/
theorem pell_8 : ∃ x y : Int, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by decide, by decide⟩

end Math

#print axioms Math.pell_8

