/-
  Brockian/GoldbachWheelK2_67.lean — exact local product K₂·K_67.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_67 from def: 1 ± 1/(p−1)^{3 or 4} with p=67 → (p−1)=66.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_67

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 67) := ⟨by decide⟩

theorem Kp_sixtySeven_of_dvd {h : ℤ} (hh : (67 : ℤ) ∣ h) :
    Kp 67 h = (287497 / 287496 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixtySeven_of_not_dvd {h : ℤ} (hh : ¬(67 : ℤ) ∣ h) :
    Kp 67 h = (18974735 / 18974736 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixtySeven (h : ℤ) :
    Kp 67 h = if (67 : ℤ) ∣ h then (287497 / 287496 : ℚ) else (18974735 / 18974736 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixtySeven_of_dvd hh
  · exact Kp_sixtySeven_of_not_dvd hh

def K2_67 (h : ℤ) : ℚ := Kp 2 h * Kp 67 h

theorem K2_67_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_67 h = 0 := by
  simp [K2_67, Kp_two_of_not_dvd h2]

theorem K2_67_of_two_and_sixtySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (67 : ℤ) ∣ h) :
    K2_67 h = (2 : ℚ) * (287497 / 287496) := by
  simp [K2_67, Kp_two_of_dvd h2, Kp_sixtySeven_of_dvd hp]

theorem K2_67_eq (h : ℤ) :
    K2_67 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (67 : ℤ) ∣ h then (287497 / 287496 : ℚ) else (18974735 / 18974736 : ℚ)) := by
  simp [K2_67, Kp_two h, Kp_sixtySeven h]

end Brockian.Goldbach.WheelK2_67
