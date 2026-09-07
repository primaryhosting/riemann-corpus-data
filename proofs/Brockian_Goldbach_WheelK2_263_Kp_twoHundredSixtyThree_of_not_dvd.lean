/-
  Brockian/GoldbachWheelK2_263.lean — exact local product K₂·K_263.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_263 from def: 1 ± 1/(p−1)^{3 or 4} with p=263 → (p−1)=262.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_263

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 263) := ⟨by decide⟩

theorem Kp_twoHundredSixtyThree_of_dvd {h : ℤ} (hh : (263 : ℤ) ∣ h) :
    Kp 263 h = (17984729 / 17984728 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSixtyThree_of_not_dvd {h : ℤ} (hh : ¬(263 : ℤ) ∣ h) :
    Kp 263 h = (4711998735 / 4711998736 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSixtyThree (h : ℤ) :
    Kp 263 h = if (263 : ℤ) ∣ h then (17984729 / 17984728 : ℚ) else (4711998735 / 4711998736 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredSixtyThree_of_dvd hh
  · exact Kp_twoHundredSixtyThree_of_not_dvd hh

def K2_263 (h : ℤ) : ℚ := Kp 2 h * Kp 263 h

theorem K2_263_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_263 h = 0 := by
  simp [K2_263, Kp_two_of_not_dvd h2]

theorem K2_263_of_two_and_twoHundredSixtyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (263 : ℤ) ∣ h) :
    K2_263 h = (2 : ℚ) * (17984729 / 17984728) := by
  simp [K2_263, Kp_two_of_dvd h2, Kp_twoHundredSixtyThree_of_dvd hp]

theorem K2_263_eq (h : ℤ) :
    K2_263 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (263 : ℤ) ∣ h then (17984729 / 17984728 : ℚ) else (4711998735 / 4711998736 : ℚ)) := by
  simp [K2_263, Kp_two h, Kp_twoHundredSixtyThree h]

end Brockian.Goldbach.WheelK2_263
