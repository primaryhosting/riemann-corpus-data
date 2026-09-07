/-
  Brockian/GoldbachWheelK2_467.lean — exact local product K₂·K_467.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_467 from def: 1 ± 1/(p−1)^{3 or 4} with p=467 → (p−1)=466.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_467

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 467) := ⟨by decide⟩

theorem Kp_fourHundredSixtySeven_of_dvd {h : ℤ} (hh : (467 : ℤ) ∣ h) :
    Kp 467 h = (101194697 / 101194696 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSixtySeven_of_not_dvd {h : ℤ} (hh : ¬(467 : ℤ) ∣ h) :
    Kp 467 h = (47156728335 / 47156728336 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSixtySeven (h : ℤ) :
    Kp 467 h = if (467 : ℤ) ∣ h then (101194697 / 101194696 : ℚ) else (47156728335 / 47156728336 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredSixtySeven_of_dvd hh
  · exact Kp_fourHundredSixtySeven_of_not_dvd hh

def K2_467 (h : ℤ) : ℚ := Kp 2 h * Kp 467 h

theorem K2_467_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_467 h = 0 := by
  simp [K2_467, Kp_two_of_not_dvd h2]

theorem K2_467_of_two_and_fourHundredSixtySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (467 : ℤ) ∣ h) :
    K2_467 h = (2 : ℚ) * (101194697 / 101194696) := by
  simp [K2_467, Kp_two_of_dvd h2, Kp_fourHundredSixtySeven_of_dvd hp]

theorem K2_467_eq (h : ℤ) :
    K2_467 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (467 : ℤ) ∣ h then (101194697 / 101194696 : ℚ) else (47156728335 / 47156728336 : ℚ)) := by
  simp [K2_467, Kp_two h, Kp_fourHundredSixtySeven h]

end Brockian.Goldbach.WheelK2_467
