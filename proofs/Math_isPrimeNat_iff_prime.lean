import Mathlib
import RequestProject.TwoSquares29

/-!
Mathlib-facing restatement of `Math.two_squares_29`: the predicate `Math.IsPrimeNat` used in
`RequestProject/TwoSquares29.lean` agrees with Mathlib's `Nat.Prime`, so `29` is a Mathlib-prime
which is a sum of two squares.
-/

namespace Math

theorem isPrimeNat_iff_prime {p : ℕ} : IsPrimeNat p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨hp, hdvd⟩
    refine Nat.prime_def.mpr ⟨hp, fun m hm => ?_⟩
    rcases hdvd m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- The prime `29` (in Mathlib's sense) is a sum of two squares. -/
theorem prime_29_sum_two_squares : Nat.Prime 29 ∧ ∃ a b : ℕ, 29 = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_iff_prime.mp isPrimeNat_29, two_squares_29.2⟩

end Math

/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: the required header above is a module docstring, and Lean 4 does not
allow `import` commands after any command (including a module docstring).  To keep the header
exactly as requested at the very beginning of the file, this development is written without
imports, using only Lean core.  Primality is therefore spelled out explicitly below via
`Math.IsPrimeNat`, which is the standard definition of a prime natural number.
-/

namespace Math

/-- A natural number is prime when it is at least `2` and its only divisors are `1` and itself. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- `29` is prime. -/
theorem isPrimeNat_29 : IsPrimeNat 29 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hle : m ≤ 29 := Nat.le_of_dvd (by decide) hm
  have key : ∀ k : Nat, k < 30 → k ∣ 29 → k = 1 ∨ k = 29 := by decide
  exact key m (Nat.lt_succ_of_le hle) hm

/-- The prime `29` is a sum of two squares: `29 = 2 ^ 2 + 5 ^ 2`. -/
theorem two_squares_29 : IsPrimeNat 29 ∧ ∃ a b : Nat, 29 = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_29, 2, 5, by decide⟩

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

