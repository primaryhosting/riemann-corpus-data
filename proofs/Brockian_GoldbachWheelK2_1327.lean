/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

set_option maxRecDepth 20000

/-- Primality by trial division: `n` is prime when `2 ≤ n` and no `m` with
`2 ≤ m < n` divides `n`. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m < n → 2 ≤ m → n % m ≠ 0

instance (n : Nat) : Decidable (IsPrime n) := by
  unfold IsPrime; infer_instance

/-- `n` lies on the wheel of modulus `m` when it is coprime to `m`, i.e. it
occupies one of the residue classes modulo `m` that primes larger than `m` can
occupy. -/
def OnWheel (m n : Nat) : Prop := Nat.gcd m n = 1

instance (m n : Nat) : Decidable (OnWheel m n) := by
  unfold OnWheel; infer_instance

/-- `1327` is prime. -/
theorem isPrime_1327 : IsPrime 1327 := by decide

/-- **Goldbach Wheel K 2, modulus 1327.**

The even number `2 * 1327 = 2654` is a sum of `K = 2` primes, each of which
lies on the wheel of modulus `6` (is coprime to `6`) and in fact occupies the
residue class `1 mod 6`. -/
theorem GoldbachWheelK2_1327 :
    ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = 2 * 1327 ∧
      OnWheel 6 p ∧ OnWheel 6 q ∧ p % 6 = 1 ∧ q % 6 = 1 :=
  ⟨1327, 1327, isPrime_1327, isPrime_1327, by decide, by decide, by decide,
    by decide, by decide⟩

end Brockian

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

