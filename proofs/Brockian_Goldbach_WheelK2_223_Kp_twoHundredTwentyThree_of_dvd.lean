/-
  Brockian/GoldbachWheelK2_223.lean — exact local product K₂·K_223.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_223 from def: 1 ± 1/(p−1)^{3 or 4} with p=223 → (p−1)=222.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_223

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 223) := ⟨by decide⟩

theorem Kp_twoHundredTwentyThree_of_dvd {h : ℤ} (hh : (223 : ℤ) ∣ h) :
    Kp 223 h = (10941049 / 10941048 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredTwentyThree_of_not_dvd {h : ℤ} (hh : ¬(223 : ℤ) ∣ h) :
    Kp 223 h = (2428912655 / 2428912656 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredTwentyThree (h : ℤ) :
    Kp 223 h = if (223 : ℤ) ∣ h then (10941049 / 10941048 : ℚ) else (2428912655 / 2428912656 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredTwentyThree_of_dvd hh
  · exact Kp_twoHundredTwentyThree_of_not_dvd hh

def K2_223 (h : ℤ) : ℚ := Kp 2 h * Kp 223 h

theorem K2_223_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_223 h = 0 := by
  simp [K2_223, Kp_two_of_not_dvd h2]

theorem K2_223_of_two_and_twoHundredTwentyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (223 : ℤ) ∣ h) :
    K2_223 h = (2 : ℚ) * (10941049 / 10941048) := by
  simp [K2_223, Kp_two_of_dvd h2, Kp_twoHundredTwentyThree_of_dvd hp]

theorem K2_223_eq (h : ℤ) :
    K2_223 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (223 : ℤ) ∣ h then (10941049 / 10941048 : ℚ) else (2428912655 / 2428912656 : ℚ)) := by
  simp [K2_223, Kp_two h, Kp_twoHundredTwentyThree h]

end Brockian.Goldbach.WheelK2_223
