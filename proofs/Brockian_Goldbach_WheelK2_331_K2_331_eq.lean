/-
  Brockian/GoldbachWheelK2_331.lean — exact local product K₂·K_331.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_331 from def: 1 ± 1/(p−1)^{3 or 4} with p=331 → (p−1)=330.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_331

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 331) := ⟨by decide⟩

theorem Kp_threeHundredThirtyOne_of_dvd {h : ℤ} (hh : (331 : ℤ) ∣ h) :
    Kp 331 h = (35937001 / 35937000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredThirtyOne_of_not_dvd {h : ℤ} (hh : ¬(331 : ℤ) ∣ h) :
    Kp 331 h = (11859209999 / 11859210000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredThirtyOne (h : ℤ) :
    Kp 331 h = if (331 : ℤ) ∣ h then (35937001 / 35937000 : ℚ) else (11859209999 / 11859210000 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredThirtyOne_of_dvd hh
  · exact Kp_threeHundredThirtyOne_of_not_dvd hh

def K2_331 (h : ℤ) : ℚ := Kp 2 h * Kp 331 h

theorem K2_331_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_331 h = 0 := by
  simp [K2_331, Kp_two_of_not_dvd h2]

theorem K2_331_of_two_and_threeHundredThirtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (331 : ℤ) ∣ h) :
    K2_331 h = (2 : ℚ) * (35937001 / 35937000) := by
  simp [K2_331, Kp_two_of_dvd h2, Kp_threeHundredThirtyOne_of_dvd hp]

theorem K2_331_eq (h : ℤ) :
    K2_331 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (331 : ℤ) ∣ h then (35937001 / 35937000 : ℚ) else (11859209999 / 11859210000 : ℚ)) := by
  simp [K2_331, Kp_two h, Kp_threeHundredThirtyOne h]

end Brockian.Goldbach.WheelK2_331
