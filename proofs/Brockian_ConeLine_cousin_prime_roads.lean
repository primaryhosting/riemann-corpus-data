/-
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- Cousin primes `(p, p+4)` with `p > 5` travel exactly the roads
`2→1`, `3→2`, `4→3` on the five-ray wheel. -/
theorem cousin_prime_roads (p : ℕ) (hp : p.Prime) (hq : (p + 4).Prime) (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have h1 : p % 5 ≠ 0 := by
    intro h
    have hdvd : (5 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 5 hdvd) with h' | h' <;> omega
  have h2 : (p + 4) % 5 ≠ 0 := by
    intro h
    have hdvd : (5 : ℕ) ∣ (p + 4) := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h' | h' <;> omega
  have h3 : (p + 4) % 5 = (p % 5 + 4) % 5 := by omega
  have h4 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (p % 5) <;> simp_all

end Brockian.ConeLine

