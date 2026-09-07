import Mathlib

namespace Brockian.PrimitiveRoot

/-!
# Primitive roots modulo small primes

A unit `a` in `(ZMod p)ˣ` is a *primitive root* mod `p` when its multiplicative
order is `p − 1`, i.e. it generates the cyclic group of units.

We characterize the order of `a` by explicit power computations in the finite
type `ZMod p`:  `a` has order `m` iff `a^m = 1` and `a^k ≠ 1` for `0 < k < m`.

All results are proved by `decide`, since `ZMod 7` and `ZMod 11` are small
finite types with decidable equality, so every power reduces to a concrete value.
-/

/-! ## mod 7  (p − 1 = 6):  3 is a primitive root, 2 is not -/

-- Powers of 3 mod 7: 3, 2, 6, 4, 5, 1 → order 6.
theorem three_pow6_mod7 : (3 : ZMod 7) ^ 6 = 1 := by decide

theorem three_order6_mod7 :
    (3 : ZMod 7) ^ 1 ≠ 1 ∧ (3 : ZMod 7) ^ 2 ≠ 1 ∧ (3 : ZMod 7) ^ 3 ≠ 1 ∧
      (3 : ZMod 7) ^ 4 ≠ 1 ∧ (3 : ZMod 7) ^ 5 ≠ 1 := by decide
-- so ord(3) = 6 = p − 1: 3 is a primitive root mod 7.

-- Powers of 2 mod 7: 2, 4, 1 → order 3.
theorem two_order3_mod7 :
    (2 : ZMod 7) ^ 3 = 1 ∧ (2 : ZMod 7) ^ 1 ≠ 1 ∧ (2 : ZMod 7) ^ 2 ≠ 1 := by decide
-- ord(2) = 3 ≠ 6, so 2 is NOT a primitive root mod 7 (honest contrast).

/-! ## mod 11  (p − 1 = 10):  2 is a primitive root, 3 is not -/

-- Powers of 2 mod 11: 2, 4, 8, 5, 10, 9, 7, 3, 6, 1 → order 10.
theorem two_pow10_mod11 : (2 : ZMod 11) ^ 10 = 1 := by decide

theorem two_order10_mod11 :
    (2 : ZMod 11) ^ 1 ≠ 1 ∧ (2 : ZMod 11) ^ 2 ≠ 1 ∧ (2 : ZMod 11) ^ 5 ≠ 1 := by decide
-- ord(2) ∣ 10 and ≠ 1, 2, 5 ⇒ ord(2) = 10 (the only divisor of 10 left):
-- 2 is a primitive root mod 11.

-- Powers of 3 mod 11: 3, 9, 5, 4, 1 → order 5.
theorem three_not_primroot_mod11 : (3 : ZMod 11) ^ 5 = 1 := by decide
-- ord(3) ∣ 5, so ord(3) ∈ {1, 5} < 10 ⇒ 3 is NOT a primitive root mod 11.

/-! ## Bundle -/

theorem primitive_roots_examples :
    (3 : ZMod 7) ^ 6 = 1 ∧ (2 : ZMod 7) ^ 3 = 1 ∧ (2 : ZMod 11) ^ 10 = 1 :=
  ⟨three_pow6_mod7, two_order3_mod7.1, two_pow10_mod11⟩

end Brockian.PrimitiveRoot
