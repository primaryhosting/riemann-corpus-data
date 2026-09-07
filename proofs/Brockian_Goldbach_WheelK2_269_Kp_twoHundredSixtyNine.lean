/-
  Brockian/GoldbachWheelK2_269.lean — exact local product K₂·K_269.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_269 from def: 1 ± 1/(p−1)^{3 or 4} with p=269 → (p−1)=268.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_269

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 269) := ⟨by decide⟩

theorem Kp_twoHundredSixtyNine_of_dvd {h : ℤ} (hh : (269 : ℤ) ∣ h) :
    Kp 269 h = (19248833 / 19248832 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSixtyNine_of_not_dvd {h : ℤ} (hh : ¬(269 : ℤ) ∣ h) :
    Kp 269 h = (5158686975 / 5158686976 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSixtyNine (h : ℤ) :
    Kp 269 h = if (269 : ℤ) ∣ h then (19248833 / 19248832 : ℚ) else (5158686975 / 5158686976 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredSixtyNine_of_dvd hh
  · exact Kp_twoHundredSixtyNine_of_not_dvd hh

def K2_269 (h : ℤ) : ℚ := Kp 2 h * Kp 269 h

theorem K2_269_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_269 h = 0 := by
  simp [K2_269, Kp_two_of_not_dvd h2]

theorem K2_269_of_two_and_twoHundredSixtyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (269 : ℤ) ∣ h) :
    K2_269 h = (2 : ℚ) * (19248833 / 19248832) := by
  simp [K2_269, Kp_two_of_dvd h2, Kp_twoHundredSixtyNine_of_dvd hp]

theorem K2_269_eq (h : ℤ) :
    K2_269 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (269 : ℤ) ∣ h then (19248833 / 19248832 : ℚ) else (5158686975 / 5158686976 : ℚ)) := by
  simp [K2_269, Kp_two h, Kp_twoHundredSixtyNine h]

end Brockian.Goldbach.WheelK2_269
