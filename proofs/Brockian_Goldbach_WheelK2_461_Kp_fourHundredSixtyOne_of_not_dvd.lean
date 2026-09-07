/-
  Brockian/GoldbachWheelK2_461.lean — exact local product K₂·K_461.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_461 from def: 1 ± 1/(p−1)^{3 or 4} with p=461 → (p−1)=460.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_461

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 461) := ⟨by decide⟩

theorem Kp_fourHundredSixtyOne_of_dvd {h : ℤ} (hh : (461 : ℤ) ∣ h) :
    Kp 461 h = (97336001 / 97336000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSixtyOne_of_not_dvd {h : ℤ} (hh : ¬(461 : ℤ) ∣ h) :
    Kp 461 h = (44774559999 / 44774560000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSixtyOne (h : ℤ) :
    Kp 461 h = if (461 : ℤ) ∣ h then (97336001 / 97336000 : ℚ) else (44774559999 / 44774560000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredSixtyOne_of_dvd hh
  · exact Kp_fourHundredSixtyOne_of_not_dvd hh

def K2_461 (h : ℤ) : ℚ := Kp 2 h * Kp 461 h

theorem K2_461_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_461 h = 0 := by
  simp [K2_461, Kp_two_of_not_dvd h2]

theorem K2_461_of_two_and_fourHundredSixtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (461 : ℤ) ∣ h) :
    K2_461 h = (2 : ℚ) * (97336001 / 97336000) := by
  simp [K2_461, Kp_two_of_dvd h2, Kp_fourHundredSixtyOne_of_dvd hp]

theorem K2_461_eq (h : ℤ) :
    K2_461 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (461 : ℤ) ∣ h then (97336001 / 97336000 : ℚ) else (44774559999 / 44774560000 : ℚ)) := by
  simp [K2_461, Kp_two h, Kp_fourHundredSixtyOne h]

end Brockian.Goldbach.WheelK2_461
