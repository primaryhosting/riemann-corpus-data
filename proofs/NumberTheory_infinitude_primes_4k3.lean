/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the required header appears above as a plain block comment and is repeated
-- as the module docstring below.)

import Mathlib

/-!
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- There are infinitely many primes congruent to `3` modulo `4`: for every `N` there
exists a prime `p` with `N < p` and `p % 4 = 3`.

Proved from Mathlib's Dirichlet theorem on primes in arithmetic progressions,
`Nat.forall_exists_prime_gt_and_modEq`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 4 = 3 := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3) (by norm_num) (by decide)
  exact ⟨p, hpN, hp, hmod⟩

end NumberTheory

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

