/-
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
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

namespace Math

/-- The Law of Quadratic Reciprocity: for distinct odd primes `p` and `q`,
`(p/q) * (q/p) = (-1) ^ (((p-1)/2) * ((q-1)/2))`, where `(· / ·)` denotes the
Legendre symbol and the exponent uses natural number subtraction and division. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp₁ : p % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out : p.Prime)).resolve_left hp
  have hq₁ : q % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out : q.Prime)).resolve_left hq
  have hep : (p - 1) / 2 = p / 2 := by omega
  have heq : (q - 1) / 2 = q / 2 := by omega
  rw [hep, heq]
  exact legendreSym.quadratic_reciprocity hp hq hpq

end Math

