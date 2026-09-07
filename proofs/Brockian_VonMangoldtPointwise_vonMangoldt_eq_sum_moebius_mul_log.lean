import Mathlib

open ArithmeticFunction

namespace Brockian.VonMangoldtPointwise

theorem vonMangoldt_eq_sum_moebius_mul_log (n : ℕ) :
    vonMangoldt n = ∑ d ∈ n.divisors, (moebius d : ℝ) * Real.log (n / d) := by
  rw [← moebius_mul_log_eq_vonMangoldt, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun a b => (moebius : ArithmeticFunction ℝ) a * log b)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply,
      Nat.cast_div hdvd hd0]

end Brockian.VonMangoldtPointwise
