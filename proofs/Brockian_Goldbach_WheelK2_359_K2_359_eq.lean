/-
  Brockian/GoldbachWheelK2_359.lean — exact local product K₂·K_359.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_359 from def: 1 ± 1/(p−1)^{3 or 4} with p=359 → (p−1)=358.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_359

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 359) := ⟨by decide⟩

theorem Kp_threeHundredFiftyNine_of_dvd {h : ℤ} (hh : (359 : ℤ) ∣ h) :
    Kp 359 h = (45882713 / 45882712 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFiftyNine_of_not_dvd {h : ℤ} (hh : ¬(359 : ℤ) ∣ h) :
    Kp 359 h = (16426010895 / 16426010896 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFiftyNine (h : ℤ) :
    Kp 359 h = if (359 : ℤ) ∣ h then (45882713 / 45882712 : ℚ) else (16426010895 / 16426010896 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredFiftyNine_of_dvd hh
  · exact Kp_threeHundredFiftyNine_of_not_dvd hh

def K2_359 (h : ℤ) : ℚ := Kp 2 h * Kp 359 h

theorem K2_359_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_359 h = 0 := by
  simp [K2_359, Kp_two_of_not_dvd h2]

theorem K2_359_of_two_and_threeHundredFiftyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (359 : ℤ) ∣ h) :
    K2_359 h = (2 : ℚ) * (45882713 / 45882712) := by
  simp [K2_359, Kp_two_of_dvd h2, Kp_threeHundredFiftyNine_of_dvd hp]

theorem K2_359_eq (h : ℤ) :
    K2_359 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (359 : ℤ) ∣ h then (45882713 / 45882712 : ℚ) else (16426010895 / 16426010896 : ℚ)) := by
  simp [K2_359, Kp_two h, Kp_threeHundredFiftyNine h]

end Brockian.Goldbach.WheelK2_359
