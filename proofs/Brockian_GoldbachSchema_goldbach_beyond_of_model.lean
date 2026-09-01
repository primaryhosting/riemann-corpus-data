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

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GoldbachSchema

/-- `GoldbachBeyond N` says that *beyond* the bound `N` there is an even number which is a
sum of two distinct primes, i.e. the Goldbach representation property is witnessed at some
even number larger than `N`. -/
def GoldbachBeyond (N : ℕ) : Prop :=
  ∃ m p q : ℕ, N < m ∧ Even m ∧ Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p + q = m

/-- The "model" hypothesis of the schema: a Bertrand-type prime model, asserting that for every
positive `n` there is a prime in the interval `(n, 2n]`. -/
def BertrandModel : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n

/-- The conditional schema: assuming the prime model, the Goldbach-beyond property holds at
every bound `N`. -/
theorem goldbach_beyond_of_model_cond (hmodel : BertrandModel) (N : ℕ) :
    GoldbachBeyond N := by
  obtain ⟨p, hp, hpN, -⟩ := hmodel (N + 2) (by omega)
  obtain ⟨q, hq, hpq, -⟩ := hmodel p hp.pos.ne'
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  refine ⟨p + q, p, q, by omega, ?_, hp, hq, by omega, rfl⟩
  exact (hp.odd_of_ne_two hp2).add_odd (hq.odd_of_ne_two hq2)

/-- Discharge of the named hypothesis: the prime model is unconditionally true.  This is exactly
**Bertrand's postulate**, available in Mathlib as `Nat.exists_prime_lt_and_le_two_mul`. -/
theorem bertrandModel_holds : BertrandModel :=
  Nat.exists_prime_lt_and_le_two_mul

/-- **Goldbach beyond, unconditional.**  For every bound `N` there is an even number `m > N`
which is the sum of two distinct primes.  The model hypothesis of the schema has been
discharged via Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`). -/
theorem goldbach_beyond_of_model (N : ℕ) : GoldbachBeyond N :=
  goldbach_beyond_of_model_cond bertrandModel_holds N

end Brockian.GoldbachSchema

