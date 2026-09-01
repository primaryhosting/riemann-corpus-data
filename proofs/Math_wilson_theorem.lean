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

namespace Math

/-- **Wilson's theorem**: for `n > 1`, `n` is prime if and only if
`(n - 1)! ≡ -1 (mod n)`. -/
theorem wilson_theorem (n : ℕ) (hn : 1 < n) :
    Nat.Prime n ↔ ((n - 1)! : ℤ) ≡ -1 [ZMOD (n : ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff, Nat.prime_iff_fac_equiv_neg_one hn.ne']
  push_cast
  rfl

end Math

