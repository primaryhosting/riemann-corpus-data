import Mathlib
namespace C6.IT5

/-- The logarithm of a product of positive reals is the sum of the logarithms.
(`Real.log_mul` in Mathlib, which only needs nonvanishing.) -/
theorem log_mul_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a*b) = Real.log a + Real.log b :=
  Real.log_mul ha.ne' hb.ne'

/-- `log (a ^ n) = n * log a` for a natural power (`Real.log_pow`; the positivity
hypothesis is not needed, but is kept as requested). -/
theorem log_pow (a : ℝ) (ha : 0 < a) (n : ℕ) : Real.log (a^n) = n * Real.log a :=
  Real.log_pow a n

/-- The exponential turns sums into products (`Real.exp_add`). -/
theorem exp_add_law (a b : ℝ) : Real.exp (a+b) = Real.exp a * Real.exp b :=
  Real.exp_add a b

end C6.IT5

