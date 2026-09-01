/- (Header kept verbatim below; Lean requires `import` before any module docstring,
   so the `/-! ... -/` block is placed immediately after the imports.) -/

import Mathlib

/-!
# Nat Cast Add
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.natCast_add
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

set_option grind.warning false

namespace Ordinal

/-- Finite-ordinal addition agrees with `Nat` addition:
the cast of a sum of naturals is the sum of the casts.
(This is `Nat.cast_add` for the `AddMonoidWithOne` structure on `Ordinal`.) -/
theorem natCast_add (m n : ℕ) : ((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal) :=
  Nat.cast_add m n

/-- Finite-ordinal multiplication agrees with `Nat` multiplication:
the cast of a product of naturals is the product of the casts.
(Mathlib already provides this as `Ordinal.natCast_mul`.) -/
theorem natCast_mul' (m n : ℕ) : ((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal) :=
  Ordinal.natCast_mul m n

end Ordinal

#print axioms Ordinal.natCast_add
#print axioms Ordinal.natCast_mul'

