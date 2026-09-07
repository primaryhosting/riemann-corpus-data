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

namespace Brockian

/-- The new wheel modulus `1327` is prime. -/
theorem prime_1327 : Nat.Prime 1327 := by norm_num

instance : Fact (Nat.Prime 1327) := ⟨prime_1327⟩

/-- Every element of `ZMod 1327` can be split as a sum of two nonzero elements. -/
theorem exists_add_eq_of_ne_zero_1327 (r : ZMod 1327) :
    ∃ a b : ZMod 1327, a ≠ 0 ∧ b ≠ 0 ∧ a + b = r := by
  by_cases h : r = 1
  · refine ⟨2, -1, ?_, ?_, ?_⟩
    · decide
    · decide
    · subst h; ring
  · refine ⟨1, r - 1, ?_, ?_, by ring⟩
    · decide
    · intro hb
      exact h (by linear_combination hb)

/-- **Goldbach wheel for the modulus `1327`, `K = 2`.**

Sums of two primes cover *every* residue class modulo the wheel modulus `1327`, and this
remains true if both primes are required to exceed an arbitrary bound `N`: for every
`r : ZMod 1327` and every `N : ℕ` there are primes `p, q > N` with `p + q ≡ r [MOD 1327]`. -/
theorem GoldbachWheelK2_1327 (r : ZMod 1327) (N : ℕ) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
      (p : ZMod 1327) + (q : ZMod 1327) = r := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_add_eq_of_ne_zero_1327 r
  obtain ⟨p, hpN, hp, hpa⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 1327) (isUnit_iff_ne_zero.mpr ha) N
  obtain ⟨q, hqN, hq, hqb⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 1327) (isUnit_iff_ne_zero.mpr hb) N
  exact ⟨p, q, hpN, hqN, hp, hq, by rw [hpa, hqb, hab]⟩

/-- Natural-number form of the Goldbach wheel for the modulus `1327`: every residue
`r < 1327` is the residue of a sum of two primes. -/
theorem GoldbachWheelK2_1327_nat (r : ℕ) (hr : r < 1327) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ (p + q) % 1327 = r := by
  obtain ⟨p, q, -, -, hp, hq, hpq⟩ := GoldbachWheelK2_1327 (r : ZMod 1327) 0
  refine ⟨p, q, hp, hq, ?_⟩
  have h : ((p + q : ℕ) : ZMod 1327) = ((r : ℕ) : ZMod 1327) := by push_cast [hpq]; ring
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using this

end Brockian

