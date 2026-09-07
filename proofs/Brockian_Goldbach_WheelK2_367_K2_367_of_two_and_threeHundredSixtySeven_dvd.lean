/-
  Brockian/GoldbachWheelK2_367.lean — exact local product K₂·K_367.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_367 from def: 1 ± 1/(p−1)^{3 or 4} with p=367 → (p−1)=366.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_367

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 367) := ⟨by decide⟩

theorem Kp_threeHundredSixtySeven_of_dvd {h : ℤ} (hh : (367 : ℤ) ∣ h) :
    Kp 367 h = (49027897 / 49027896 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSixtySeven_of_not_dvd {h : ℤ} (hh : ¬(367 : ℤ) ∣ h) :
    Kp 367 h = (17944209935 / 17944209936 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSixtySeven (h : ℤ) :
    Kp 367 h = if (367 : ℤ) ∣ h then (49027897 / 49027896 : ℚ) else (17944209935 / 17944209936 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredSixtySeven_of_dvd hh
  · exact Kp_threeHundredSixtySeven_of_not_dvd hh

def K2_367 (h : ℤ) : ℚ := Kp 2 h * Kp 367 h

theorem K2_367_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_367 h = 0 := by
  simp [K2_367, Kp_two_of_not_dvd h2]

theorem K2_367_of_two_and_threeHundredSixtySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (367 : ℤ) ∣ h) :
    K2_367 h = (2 : ℚ) * (49027897 / 49027896) := by
  simp [K2_367, Kp_two_of_dvd h2, Kp_threeHundredSixtySeven_of_dvd hp]

theorem K2_367_eq (h : ℤ) :
    K2_367 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (367 : ℤ) ∣ h then (49027897 / 49027896 : ℚ) else (17944209935 / 17944209936 : ℚ)) := by
  simp [K2_367, Kp_two h, Kp_threeHundredSixtySeven h]

end Brockian.Goldbach.WheelK2_367
