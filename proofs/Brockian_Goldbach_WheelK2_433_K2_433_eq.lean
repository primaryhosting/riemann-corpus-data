/-
  Brockian/GoldbachWheelK2_433.lean — exact local product K₂·K_433.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_433 from def: 1 ± 1/(p−1)^{3 or 4} with p=433 → (p−1)=432.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_433

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 433) := ⟨by decide⟩

theorem Kp_fourHundredThirtyThree_of_dvd {h : ℤ} (hh : (433 : ℤ) ∣ h) :
    Kp 433 h = (80621569 / 80621568 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredThirtyThree_of_not_dvd {h : ℤ} (hh : ¬(433 : ℤ) ∣ h) :
    Kp 433 h = (34828517375 / 34828517376 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredThirtyThree (h : ℤ) :
    Kp 433 h = if (433 : ℤ) ∣ h then (80621569 / 80621568 : ℚ) else (34828517375 / 34828517376 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredThirtyThree_of_dvd hh
  · exact Kp_fourHundredThirtyThree_of_not_dvd hh

def K2_433 (h : ℤ) : ℚ := Kp 2 h * Kp 433 h

theorem K2_433_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_433 h = 0 := by
  simp [K2_433, Kp_two_of_not_dvd h2]

theorem K2_433_of_two_and_fourHundredThirtyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (433 : ℤ) ∣ h) :
    K2_433 h = (2 : ℚ) * (80621569 / 80621568) := by
  simp [K2_433, Kp_two_of_dvd h2, Kp_fourHundredThirtyThree_of_dvd hp]

theorem K2_433_eq (h : ℤ) :
    K2_433 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (433 : ℤ) ∣ h then (80621569 / 80621568 : ℚ) else (34828517375 / 34828517376 : ℚ)) := by
  simp [K2_433, Kp_two h, Kp_fourHundredThirtyThree h]

end Brockian.Goldbach.WheelK2_433
