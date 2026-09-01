/-
# Bertrand
Category: Frontier — Prime Numbers
Target: Primes.bertrand
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bertrand
Category: Frontier — Prime Numbers
Target: Primes.bertrand
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Primes

/-- **Bertrand's postulate**: for every natural number `n` with `0 < n` there exists a prime `p`
with `n < p` and `p ≤ 2 * n`.  This follows directly from Mathlib's
`Nat.exists_prime_lt_and_le_two_mul` (`Mathlib/NumberTheory/Bertrand.lean`). -/
theorem bertrand (n : ℕ) (hn : 0 < n) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n hn.ne'

end Primes

#print axioms Primes.bertrand

