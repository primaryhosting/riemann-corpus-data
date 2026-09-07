/-
  Brockian/GoldbachWheelK2_463.lean — exact local product K₂·K_463.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_463 from def: 1 ± 1/(p−1)^{3 or 4} with p=463 → (p−1)=462.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_463

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 463) := ⟨by decide⟩

theorem Kp_fourHundredSixtyThree_of_dvd {h : ℤ} (hh : (463 : ℤ) ∣ h) :
    Kp 463 h = (98611129 / 98611128 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSixtyThree_of_not_dvd {h : ℤ} (hh : ¬(463 : ℤ) ∣ h) :
    Kp 463 h = (45558341135 / 45558341136 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSixtyThree (h : ℤ) :
    Kp 463 h = if (463 : ℤ) ∣ h then (98611129 / 98611128 : ℚ) else (45558341135 / 45558341136 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredSixtyThree_of_dvd hh
  · exact Kp_fourHundredSixtyThree_of_not_dvd hh

def K2_463 (h : ℤ) : ℚ := Kp 2 h * Kp 463 h

theorem K2_463_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_463 h = 0 := by
  simp [K2_463, Kp_two_of_not_dvd h2]

theorem K2_463_of_two_and_fourHundredSixtyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (463 : ℤ) ∣ h) :
    K2_463 h = (2 : ℚ) * (98611129 / 98611128) := by
  simp [K2_463, Kp_two_of_dvd h2, Kp_fourHundredSixtyThree_of_dvd hp]

theorem K2_463_eq (h : ℤ) :
    K2_463 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (463 : ℤ) ∣ h then (98611129 / 98611128 : ℚ) else (45558341135 / 45558341136 : ℚ)) := by
  simp [K2_463, Kp_two h, Kp_fourHundredSixtyThree h]

end Brockian.Goldbach.WheelK2_463
