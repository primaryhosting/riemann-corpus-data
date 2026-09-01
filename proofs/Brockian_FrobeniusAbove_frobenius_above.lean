import Mathlib
namespace Brockian.FrobeniusAbove
/-- Every integer strictly above the Frobenius number ab−a−b is a nonneg combination of a,b. -/
theorem frobenius_above (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hcop : Nat.Coprime a b) (m : ℕ) (hm : a * b - a - b < m) :
    ∃ x y : ℕ, a * x + b * y = m := by
  have haeq : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
  have hbeq : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
  have hid : a * b + 1 = (a - 1) * (b - 1) + a + b := by
    calc
      a * b + 1 = ((a - 1) + 1) * ((b - 1) + 1) + 1 := by rw [haeq, hbeq]
      _ = (a - 1) * (b - 1) + ((a - 1) + 1) + ((b - 1) + 1) := by ring
      _ = (a - 1) * (b - 1) + a + b := by rw [haeq, hbeq]
  have hbound : a.pred * b.pred ≤ m := by
    rw [Nat.pred_eq_sub_one, Nat.pred_eq_sub_one]
    omega
  have hgcd : a.gcd b ∣ m := by
    rw [hcop.gcd_eq_one]
    exact one_dvd m
  obtain ⟨x, y, hxy⟩ :=
    Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le a b m hgcd hbound
  exact ⟨x, y, by simpa [Nat.mul_comm] using hxy⟩
end Brockian.FrobeniusAbove

