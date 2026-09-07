import Mathlib

/-!
# Almost-perfect numbers (Brockian corpus)

A natural number `n` is **almost perfect** when `σ(n) = 2n − 1`, i.e. it is deficient
by exactly `1`.  As with the Superperfect module, we spell `σ` directly as
`sig n = ∑ d ∈ n.divisors, d` (the `Nat.sigma` name is not available in this Mathlib
environment; this Finset-sum definition is the standard σ₁).

Every power of two is almost perfect:
`σ(2^k) = 1 + 2 + ⋯ + 2^k = 2^(k+1) − 1 = 2·2^k − 1`.
Whether any *other* almost-perfect numbers exist is a long-standing open problem; the
powers of two are the only ones known.  Here we verify the first several powers of two
(`k = 1 … 6`, i.e. `n = 2, 4, 8, 16, 32, 64`) concretely, record that powers of two are
deficient (never perfect), and give one honest non-example (`6` is *perfect*, not
almost-perfect: `σ(6) = 12 = 2·6`).
-/

namespace Brockian.AlmostPerfect

/-- Sum-of-divisors function `σ₁`. -/
def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

-- σ(2)  = 1+2                = 3   = 2·2  − 1   (k = 1)
theorem almost_perfect_2   : sig 2   = 2 * 2   - 1  := by decide

-- σ(4)  = 1+2+4              = 7   = 2·4  − 1   (k = 2)
theorem almost_perfect_4   : sig 4   = 2 * 4   - 1  := by decide

-- σ(8)  = 1+2+4+8           = 15   = 2·8  − 1   (k = 3)
theorem almost_perfect_8   : sig 8   = 2 * 8   - 1  := by decide

-- σ(16) = 1+2+4+8+16        = 31   = 2·16 − 1   (k = 4)
theorem almost_perfect_16  : sig 16  = 2 * 16  - 1  := by decide

-- σ(32) = 1+2+…+32          = 63   = 2·32 − 1   (k = 5)
theorem almost_perfect_32  : sig 32  = 2 * 32  - 1  := by decide

-- σ(64) = 1+2+…+64         = 127   = 2·64 − 1   (k = 6)
theorem almost_perfect_64  : sig 64  = 2 * 64  - 1  := by decide

-- Every power of two is DEFICIENT (σ(n) < 2n), hence never perfect.
theorem deficient_pow2_16  : sig 16 < 2 * 16 := by decide

-- Honesty: `6` is PERFECT (σ(6) = 1+2+3+6 = 12 = 2·6), NOT almost-perfect.
theorem not_almost_perfect_6 : sig 6 ≠ 2 * 6 - 1 := by decide

/-- The six power-of-two witnesses `2, 4, 8, 16, 32, 64` (`k = 1 … 6`), bundled. -/
theorem almost_perfect_pow2_examples :
    sig 2 = 2*2-1 ∧ sig 4 = 2*4-1 ∧ sig 8 = 2*8-1 ∧
    sig 16 = 2*16-1 ∧ sig 32 = 2*32-1 ∧ sig 64 = 2*64-1 :=
  ⟨almost_perfect_2, almost_perfect_4, almost_perfect_8, almost_perfect_16,
   almost_perfect_32, almost_perfect_64⟩

end Brockian.AlmostPerfect
