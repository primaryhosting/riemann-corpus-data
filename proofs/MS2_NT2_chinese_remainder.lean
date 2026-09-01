import Mathlib
namespace MS2.NT2

theorem chinese_remainder (m n : ℕ) (h : Nat.Coprime m n) :
    Nonempty (ZMod (m*n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

theorem euler_theorem (n : ℕ) (a : ZMod n) (ha : IsUnit a) : a ^ (Nat.totient n) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]

theorem sum_two_squares_prime (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) : ∃ a b : ℕ, a^2+b^2 = p :=
  Nat.Prime.sq_add_sq (by omega)

/-- As stated, the conclusion is an implication into `True`, hence trivially provable.
A genuine form of Lucas' theorem is proved below as `lucas_theorem_eq`. -/
theorem lucas_theorem (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    (Nat.choose a b : ZMod p) =
      ∏ i ∈ Finset.range 64, ((Nat.choose ((a/p^i)%p) ((b/p^i)%p)) : ZMod p) → True :=
  fun _ => trivial

/-- **Lucas' theorem** (the intended content of `lucas_theorem`): for a prime `p` and
`a, b < p ^ 64`, the binomial coefficient `a.choose b` equals, in `ZMod p`, the product of the
binomial coefficients of the base-`p` digits of `a` and `b`. -/
theorem lucas_theorem_eq (p : ℕ) [Fact p.Prime] (a b : ℕ) (ha : a < p ^ 64) (hb : b < p ^ 64) :
    (Nat.choose a b : ZMod p) =
      ∏ i ∈ Finset.range 64, ((Nat.choose ((a/p^i)%p) ((b/p^i)%p)) : ZMod p) := by
  have h := Choose.choose_modEq_prod_range_choose_nat (p := p) ha hb
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  push_cast at h2
  exact h2

theorem mobius_inversion (f g : ℕ → ℤ) (h : ∀ n, 0 < n → g n = ∑ d ∈ Nat.divisors n, f d) (n : ℕ)
    (hn : 0 < n) :
    f n = ∑ d ∈ Nat.divisors n, (ArithmeticFunction.moebius (n/d)) * g d := by
  have h' : ∀ m : ℕ, 0 < m → ∑ d ∈ Nat.divisors m, f d = g m := fun m hm => (h m hm).symm
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)).mp h' n hn
  rw [← key]
  simp only [Int.cast_id]
  exact Nat.sum_divisorsAntidiagonal' (fun x y => (ArithmeticFunction.moebius x : ℤ) * g y)

end MS2.NT2

