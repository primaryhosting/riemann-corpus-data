import Mathlib
namespace Brockian.KummerTheorem
/-- Kummer's theorem (digit-sum form): for a prime p, the p-adic valuation of C(m+n, m),
    times (p−1), equals S_p(m) + S_p(n) − S_p(m+n), where S_p is the base-p digit sum
    (equivalently, the number of carries when adding m and n in base p). -/
theorem kummer (p m n : ℕ) (hp : p.Prime) :
    (Nat.choose (m + n) m).factorization p * (p - 1) =
      (Nat.digits p m).sum + (Nat.digits p n).sum - (Nat.digits p (m + n)).sum := by
  have hmle : m ≤ m + n := Nat.le_add_right m n
  have hchoose : Nat.choose (m + n) m ≠ 0 := Nat.choose_ne_zero hmle
  have hfact : Nat.choose (m + n) m * m.factorial * n.factorial = (m + n).factorial := by
    simpa using Nat.choose_mul_factorial_mul_factorial hmle
  have hv := congrArg (fun x : ℕ => x.factorization p) hfact
  change ((Nat.choose (m + n) m * m.factorial * n.factorial).factorization p) =
    ((m + n).factorial.factorization p) at hv
  simp only [Nat.factorization_mul hchoose m.factorial_ne_zero,
      Nat.factorization_mul (mul_ne_zero hchoose m.factorial_ne_zero) n.factorial_ne_zero] at hv
  have hvp : (Nat.choose (m + n) m).factorization p + m.factorial.factorization p +
      n.factorial.factorization p = (m + n).factorial.factorization p := hv
  have hm := Nat.sub_one_mul_factorization_factorial (n := m) hp
  have hn := Nat.sub_one_mul_factorization_factorial (n := n) hp
  have hmn := Nat.sub_one_mul_factorization_factorial (n := m + n) hp
  have hvp_mul := congrArg (fun x : ℕ => (p - 1) * x) hvp
  simp only [Nat.mul_add, hm, hn, hmn] at hvp_mul
  have hsm : (Nat.digits p m).sum ≤ m := Nat.digit_sum_le p m
  have hsn : (Nat.digits p n).sum ≤ n := Nat.digit_sum_le p n
  have hsmn : (Nat.digits p (m + n)).sum ≤ m + n := Nat.digit_sum_le p (m + n)
  have hcarry : (Nat.digits p (m + n)).sum ≤
      (Nat.digits p m).sum + (Nat.digits p n).sum := by
    omega
  have hfinal : (p - 1) * (Nat.choose (m + n) m).factorization p +
      (Nat.digits p (m + n)).sum =
      (Nat.digits p m).sum + (Nat.digits p n).sum := by
    omega
  rw [Nat.mul_comm]
  exact Nat.eq_sub_of_add_eq hfinal
end Brockian.KummerTheorem

