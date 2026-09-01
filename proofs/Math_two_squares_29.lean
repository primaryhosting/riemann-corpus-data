import Mathlib
/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 29.** The number `29` is prime, and it is a sum of two squares,
namely `29 = 2 ^ 2 + 5 ^ 2`. -/
theorem two_squares_29 : Nat.Prime 29 ∧ ∃ a b : ℕ, 29 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 2, 5, by norm_num⟩

end Math

