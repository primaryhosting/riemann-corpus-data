import Mathlib

/-!
# Two Squares 113 — Mathlib derivation

A second proof that `113` is a sum of two squares, obtained from Mathlib's
`Nat.Prime.sq_add_sq` (Fermat's Christmas theorem: a prime `p` with `p % 4 ≠ 3`
is a sum of two squares), applied to the prime `113`, which satisfies `113 % 4 = 1`.
-/

namespace Math

/-- `113` is a sum of two squares, via Fermat's Christmas theorem. -/
theorem two_squares_113_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 113 := by
  haveI : Fact (Nat.Prime 113) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 113) (by norm_num)

end Math

/-!
# Two Squares 113
Category: Pure Mathematics
Target: Math.two_squares_113
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment must be the first thing in the file, and Lean forbids
-- `import` commands after a module docstring, so this file is kept import-free.
-- A Mathlib-based derivation (via `Nat.Prime.sq_add_sq`, Fermat's Christmas theorem) is
-- given in `RequestProject/MathFermat.lean`.

namespace Math

/-- The prime `113` is a sum of two squares: `113 = 7 ^ 2 + 8 ^ 2`. -/
theorem two_squares_113 : ∃ a b : Nat, a ^ 2 + b ^ 2 = 113 := ⟨7, 8, rfl⟩

end Math

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

