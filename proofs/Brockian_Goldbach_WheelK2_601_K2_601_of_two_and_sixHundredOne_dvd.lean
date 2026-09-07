/-
  Brockian/GoldbachWheelK2_601.lean — exact local product K₂·K_601.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_601 from def: 1 ± 1/(p−1)^{3 or 4} with p=601 → (p−1)=600.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_601

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 601) := ⟨by decide⟩

theorem Kp_sixHundredOne_of_dvd {h : ℤ} (hh : (601 : ℤ) ∣ h) :
    Kp 601 h = (216000001 / 216000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredOne_of_not_dvd {h : ℤ} (hh : ¬(601 : ℤ) ∣ h) :
    Kp 601 h = (129599999999 / 129600000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredOne (h : ℤ) :
    Kp 601 h = if (601 : ℤ) ∣ h then (216000001 / 216000000 : ℚ) else (129599999999 / 129600000000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredOne_of_dvd hh
  · exact Kp_sixHundredOne_of_not_dvd hh

def K2_601 (h : ℤ) : ℚ := Kp 2 h * Kp 601 h

theorem K2_601_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_601 h = 0 := by
  simp [K2_601, Kp_two_of_not_dvd h2]

theorem K2_601_of_two_and_sixHundredOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (601 : ℤ) ∣ h) :
    K2_601 h = (2 : ℚ) * (216000001 / 216000000) := by
  simp [K2_601, Kp_two_of_dvd h2, Kp_sixHundredOne_of_dvd hp]

theorem K2_601_eq (h : ℤ) :
    K2_601 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (601 : ℤ) ∣ h then (216000001 / 216000000 : ℚ) else (129599999999 / 129600000000 : ℚ)) := by
  simp [K2_601, Kp_two h, Kp_sixHundredOne h]

end Brockian.Goldbach.WheelK2_601
