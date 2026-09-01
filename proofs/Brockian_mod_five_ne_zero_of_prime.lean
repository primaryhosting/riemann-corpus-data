import Mathlib

/-!
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- A prime `n > 5` is not divisible by `5`, i.e. `n % 5 ≠ 0`. -/
theorem mod_five_ne_zero_of_prime {n : ℕ} (hn : n.Prime) (h5 : 5 < n) : n % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h1 <;> omega

/-- Cousin primes `p`, `p + 4` with `p > 5` occupy exactly the residue "roads"
`2 → 1`, `3 → 2`, `4 → 3` on the five-ray wheel. -/
theorem cousin_prime_roads {p : ℕ} (hp : p.Prime) (hq : (p + 4).Prime) (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have hp0 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have hq0 : (p + 4) % 5 ≠ 0 := mod_five_ne_zero_of_prime hq (by omega)
  have hmod : (p + 4) % 5 = (p % 5 + 4) % 5 := by omega
  simp only [Prod.mk.injEq]
  omega

end ConeLine
end Brockian

