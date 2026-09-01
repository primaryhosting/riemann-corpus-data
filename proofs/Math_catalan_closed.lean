import Mathlib

/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede all other content, including
-- module doc comments, so the header block above sits immediately after the import.

namespace Math

/-- The `n`-th Catalan number equals `C(2n, n) / (n + 1)`.  Since `n + 1` divides
`Nat.choose (2 * n) n`, the natural-number division here is exact; this is recorded
by the companion statement `Math.catalan_closed_mul`. -/
theorem catalan_closed (n : ℕ) : catalan n = Nat.choose (2 * n) n / (n + 1) :=
  catalan_eq_centralBinom_div n

/-- Exact (division-free) form: `(n + 1) * catalan n = C(2n, n)`. -/
theorem catalan_closed_mul (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n :=
  succ_mul_catalan_eq_centralBinom n

end Math

#print axioms Math.catalan_closed
#print axioms Math.catalan_closed_mul

