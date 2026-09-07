/-
  Brockian/GoldbachWheelK2_397.lean — exact local product K₂·K_397.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_397 from def: 1 ± 1/(p−1)^{3 or 4} with p=397 → (p−1)=396.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_397

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 397) := ⟨by decide⟩

theorem Kp_threeHundredNinetySeven_of_dvd {h : ℤ} (hh : (397 : ℤ) ∣ h) :
    Kp 397 h = (62099137 / 62099136 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredNinetySeven_of_not_dvd {h : ℤ} (hh : ¬(397 : ℤ) ∣ h) :
    Kp 397 h = (24591257855 / 24591257856 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredNinetySeven (h : ℤ) :
    Kp 397 h = if (397 : ℤ) ∣ h then (62099137 / 62099136 : ℚ) else (24591257855 / 24591257856 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredNinetySeven_of_dvd hh
  · exact Kp_threeHundredNinetySeven_of_not_dvd hh

def K2_397 (h : ℤ) : ℚ := Kp 2 h * Kp 397 h

theorem K2_397_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_397 h = 0 := by
  simp [K2_397, Kp_two_of_not_dvd h2]

theorem K2_397_of_two_and_threeHundredNinetySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (397 : ℤ) ∣ h) :
    K2_397 h = (2 : ℚ) * (62099137 / 62099136) := by
  simp [K2_397, Kp_two_of_dvd h2, Kp_threeHundredNinetySeven_of_dvd hp]

theorem K2_397_eq (h : ℤ) :
    K2_397 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (397 : ℤ) ∣ h then (62099137 / 62099136 : ℚ) else (24591257855 / 24591257856 : ℚ)) := by
  simp [K2_397, Kp_two h, Kp_threeHundredNinetySeven h]

end Brockian.Goldbach.WheelK2_397
