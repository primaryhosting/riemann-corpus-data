/-!
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
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

namespace Brockian.ConeLine

/-- If `n` is prime and `5 < n`, then `n % 5 ≠ 0`. -/
lemma mod_five_ne_zero_of_prime {n : ℕ} (hn : n.Prime) (h5 : 5 < n) : n % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h1 <;> omega

/-- Cousin primes `(p, p+4)` with `p > 5` satisfy `p % 5 ∈ {2,3,4}`, and the
partner's residue is one less: the roads `2→1`, `3→2`, `4→3`. -/
theorem cousin_prime_roads {p : ℕ} (hp : p.Prime) (hq : (p + 4).Prime) (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have h1 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have h2 : (p + 4) % 5 ≠ 0 := mod_five_ne_zero_of_prime hq (by omega)
  have h3 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h4 : (p + 4) % 5 = (p % 5 + 4) % 5 := by omega
  interval_cases h : (p % 5) <;> simp_all <;> omega

end Brockian.ConeLine

