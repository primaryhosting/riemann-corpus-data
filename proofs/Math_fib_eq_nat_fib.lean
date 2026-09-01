import Mathlib
import RequestProject.Math

/-!
# Cassini 10, via Mathlib's Fibonacci numbers

This file links `Math.fib` (defined in `RequestProject.Math`, which cannot carry an `import`
line) with Mathlib's `Nat.fib`, and derives the `n = 10` case of Cassini's identity from
Mathlib's general statement `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- **Cassini's identity at `n = 10`** for Mathlib's `Nat.fib`:
`F 9 * F 11 - (F 10)^2 = (-1)^10`.

Proved as an instance of Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_10_nat_fib :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 10
  rw [show (10 : ℤ) + 1 = ((11 : ℕ) : ℤ) by norm_num,
    show (10 : ℤ) - 1 = ((9 : ℕ) : ℤ) by norm_num,
    show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num, Int.fib_natCast, Int.fib_natCast,
    Int.fib_natCast] at h
  simpa [mul_comm] using h

/-- The two formulations agree. -/
theorem cassini_10_iff_nat_fib :
    ((Math.fib 9 : ℤ) * (Math.fib 11 : ℤ) - (Math.fib 10 : ℤ) ^ 2 = (-1) ^ 10) ↔
      ((Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10) := by
  simp [fib_eq_nat_fib]

end Math

/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence `F` with `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file carries the required header comment as its first token, which Lean only permits
in a file with no `import` lines, so the sequence is defined here from scratch;
`RequestProject.MathCassini` proves `Math.fib = Nat.fib` and restates the identity
using Mathlib's Fibonacci numbers.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 10`**: `F 9 * F 11 - (F 10)^2 = (-1)^10`, computed in `ℤ`. -/
theorem cassini_10 :
    (fib 9 : Int) * (fib 11 : Int) - (fib 10 : Int) ^ 2 = (-1) ^ 10 := by
  decide

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

