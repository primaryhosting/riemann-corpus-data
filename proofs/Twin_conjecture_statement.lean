/-
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Twin.conjecture_statement
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

set_option grind.warning false

namespace Twin

/-- The twin prime conjecture: for every natural number `N` there is a prime `p > N`
such that `p + 2` is also prime. This is only *stated*, not proved. -/
def TwinPrimeConj : Prop :=
  ∀ N : Nat, ∃ p : Nat, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Well-formedness/registration lemma: the statement `TwinPrimeConj` is a well-formed
`Prop`, equivalent to itself. This is **not** a proof of the twin prime conjecture. -/
theorem conjecture_statement : TwinPrimeConj ↔ TwinPrimeConj := Iff.rfl

end Twin

