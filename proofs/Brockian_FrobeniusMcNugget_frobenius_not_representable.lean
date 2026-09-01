import Mathlib
namespace Brockian.FrobeniusMcNugget
/-- The Frobenius number ab−a−b of coprime a,b>1 is not a nonnegative integer combination. -/
theorem frobenius_not_representable (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hcop : Nat.Coprime a b) : ¬ ∃ x y : ℕ, a * x + b * y = a * b - a - b := by
  rintro ⟨x, y, hxy⟩
  have hab : a + b ≤ a * b := by nlinarith
  have hsub : a * b - (a + b) = a * x + b * y := by
    rw [← Nat.sub_sub]
    exact hxy.symm
  have habEq : a * b = (a * x + b * y) + (a + b) :=
    (Nat.sub_eq_iff_eq_add hab).mp hsub
  have heq : a * (x + 1) + b * (y + 1) = a * b := by
    calc
      _ = (a * x + b * y) + (a + b) := by ring
      _ = _ := habEq.symm
  have hsum : b ∣ a * (x + 1) + b * (y + 1) := by
    rw [heq]
    exact dvd_mul_left b a
  have hterm : b ∣ a * (x + 1) := by
    exact (Nat.dvd_add_iff_left (dvd_mul_right b (y + 1))).mpr hsum
  have hdiv : b ∣ x + 1 := by
    exact hcop.symm.dvd_of_dvd_mul_left hterm
  have hle : b ≤ x + 1 := Nat.le_of_dvd (by omega) hdiv
  nlinarith
end Brockian.FrobeniusMcNugget

