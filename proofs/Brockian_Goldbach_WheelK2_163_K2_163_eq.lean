/-
  Brockian/GoldbachWheelK2_163.lean — exact local product K₂·K_163.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_163 from def: 1 ± 1/(p−1)^{3 or 4} with p=163 → (p−1)=162.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_163

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 163) := ⟨by decide⟩

theorem Kp_oneHundredSixtyThree_of_dvd {h : ℤ} (hh : (163 : ℤ) ∣ h) :
    Kp 163 h = (4251529 / 4251528 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSixtyThree_of_not_dvd {h : ℤ} (hh : ¬(163 : ℤ) ∣ h) :
    Kp 163 h = (688747535 / 688747536 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSixtyThree (h : ℤ) :
    Kp 163 h = if (163 : ℤ) ∣ h then (4251529 / 4251528 : ℚ) else (688747535 / 688747536 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredSixtyThree_of_dvd hh
  · exact Kp_oneHundredSixtyThree_of_not_dvd hh

def K2_163 (h : ℤ) : ℚ := Kp 2 h * Kp 163 h

theorem K2_163_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_163 h = 0 := by
  simp [K2_163, Kp_two_of_not_dvd h2]

theorem K2_163_of_two_and_oneHundredSixtyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (163 : ℤ) ∣ h) :
    K2_163 h = (2 : ℚ) * (4251529 / 4251528) := by
  simp [K2_163, Kp_two_of_dvd h2, Kp_oneHundredSixtyThree_of_dvd hp]

theorem K2_163_eq (h : ℤ) :
    K2_163 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (163 : ℤ) ∣ h then (4251529 / 4251528 : ℚ) else (688747535 / 688747536 : ℚ)) := by
  simp [K2_163, Kp_two h, Kp_oneHundredSixtyThree h]

end Brockian.Goldbach.WheelK2_163
