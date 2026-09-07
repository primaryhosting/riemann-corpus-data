/-
  Brockian/GoldbachWheelK2_311.lean — exact local product K₂·K_311.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_311 from def: 1 ± 1/(p−1)^{3 or 4} with p=311 → (p−1)=310.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_311

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 311) := ⟨by decide⟩

theorem Kp_threeHundredEleven_of_dvd {h : ℤ} (hh : (311 : ℤ) ∣ h) :
    Kp 311 h = (29791001 / 29791000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredEleven_of_not_dvd {h : ℤ} (hh : ¬(311 : ℤ) ∣ h) :
    Kp 311 h = (9235209999 / 9235210000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredEleven (h : ℤ) :
    Kp 311 h = if (311 : ℤ) ∣ h then (29791001 / 29791000 : ℚ) else (9235209999 / 9235210000 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredEleven_of_dvd hh
  · exact Kp_threeHundredEleven_of_not_dvd hh

def K2_311 (h : ℤ) : ℚ := Kp 2 h * Kp 311 h

theorem K2_311_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_311 h = 0 := by
  simp [K2_311, Kp_two_of_not_dvd h2]

theorem K2_311_of_two_and_threeHundredEleven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (311 : ℤ) ∣ h) :
    K2_311 h = (2 : ℚ) * (29791001 / 29791000) := by
  simp [K2_311, Kp_two_of_dvd h2, Kp_threeHundredEleven_of_dvd hp]

theorem K2_311_eq (h : ℤ) :
    K2_311 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (311 : ℤ) ∣ h then (29791001 / 29791000 : ℚ) else (9235209999 / 9235210000 : ℚ)) := by
  simp [K2_311, Kp_two h, Kp_threeHundredEleven h]

end Brockian.Goldbach.WheelK2_311
