/-
/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-
The header block above is reproduced verbatim at the very top of the file; Lean 4 only accepts
a module docstring (`/-! ... -/`) *after* the `import` lines, so it is wrapped in an outer
block comment there and repeated as the genuine module docstring below.
-/

/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- **Goldbach wheel, `K = 2`, new wheel modulus `1153`.**

The informal title is read as follows: `1153` is proposed as a new wheel modulus, so it must
itself be prime (a Goldbach wheel modulus is built from primes), and the `K = 2` Goldbach
condition at that modulus asks for the even number `2 * 1153 = 2306` to be written as a sum of
two primes — here in two essentially different ways: the diagonal representation
`1153 + 1153` and a representation by two *distinct* primes.

Concretely we prove:

* `1153` is prime;
* `1153 + 1153 = 2 * 1153`, a Goldbach representation of `2306`;
* `13` and `2293` are distinct primes with `13 + 2293 = 2 * 1153`.

Each primality fact is discharged by `norm_num`, i.e. by Mathlib's `Nat.Prime` norm_num
extension (`Mathlib.Tactic.NormNum.Prime`).
-/
theorem GoldbachWheelK2_1153 :
    Nat.Prime 1153 ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * 1153) ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * 1153) :=
  ⟨by norm_num,
    ⟨1153, 1153, by norm_num, by norm_num, by norm_num⟩,
    ⟨13, 2293, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

end Brockian

