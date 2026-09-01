import Mathlib
namespace C3.NT5

/-- Euler's criterion: the Legendre symbol `(a/p)`, viewed in `ZMod p`, equals
`a ^ ((p-1)/2)` for an odd prime `p`. -/
theorem legendre_euler (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ℤ) :
    (legendreSym p a : ZMod p) = (a : ZMod p) ^ ((p-1)/2) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨k, hk⟩ := hodd
  have h1 : (p - 1) / 2 = p / 2 := by omega
  rw [h1]
  exact legendreSym.eq_pow p a

/-- The sum-of-divisors function `σ₁` is multiplicative.
(The original statement used the non-existent name `Nat.sigma`; it is spelled
`ArithmeticFunction.sigma` in Mathlib.) -/
theorem sum_divisors_mult (m n : ℕ) (h : Nat.Coprime m n) :
    ArithmeticFunction.sigma 1 (m * n)
      = ArithmeticFunction.sigma 1 m * ArithmeticFunction.sigma 1 n :=
  (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

/-- Wilson's theorem: `(p-1)! ≡ -1 [MOD p]` for a prime `p`. -/
theorem wilson_thm (p : ℕ) (hp : p.Prime) : ((p-1).factorial : ZMod p) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ZMod.wilsons_lemma p

end C3.NT5

