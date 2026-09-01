/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 5·y² = 1` has a nontrivial integer solution,
i.e. a solution with `y ≠ 0`. Witness: `(x, y) = (9, 4)`, since `81 - 5 * 16 = 1`. -/
theorem pell_5 : ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by decide, by decide⟩

end Math

