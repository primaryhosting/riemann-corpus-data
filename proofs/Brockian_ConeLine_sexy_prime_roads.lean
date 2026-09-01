/-
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
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

/-- A sexy prime pair `(p, p + 6)` with `p > 5` travels exactly the roads
`1 → 2`, `2 → 3`, `3 → 4` modulo `5`. -/
theorem sexy_prime_roads (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (p + 6))
    (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have hnp : ¬ (5 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h
    omega
  have hnq : ¬ (5 ∣ (p + 6)) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp h
    omega
  have h1 : p % 5 ≠ 0 := fun h => hnp (Nat.dvd_of_mod_eq_zero h)
  have h2 : (p + 6) % 5 ≠ 0 := fun h => hnq (Nat.dvd_of_mod_eq_zero h)
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

