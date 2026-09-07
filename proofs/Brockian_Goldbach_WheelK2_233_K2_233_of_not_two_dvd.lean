/-
  Brockian/GoldbachWheelK2_233.lean — exact local product K₂·K_233.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_233 from def: 1 ± 1/(p−1)^{3 or 4} with p=233 → (p−1)=232.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_233

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 233) := ⟨by decide⟩

theorem Kp_twoHundredThirtyThree_of_dvd {h : ℤ} (hh : (233 : ℤ) ∣ h) :
    Kp 233 h = (12487169 / 12487168 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredThirtyThree_of_not_dvd {h : ℤ} (hh : ¬(233 : ℤ) ∣ h) :
    Kp 233 h = (2897022975 / 2897022976 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredThirtyThree (h : ℤ) :
    Kp 233 h = if (233 : ℤ) ∣ h then (12487169 / 12487168 : ℚ) else (2897022975 / 2897022976 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredThirtyThree_of_dvd hh
  · exact Kp_twoHundredThirtyThree_of_not_dvd hh

def K2_233 (h : ℤ) : ℚ := Kp 2 h * Kp 233 h

theorem K2_233_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_233 h = 0 := by
  simp [K2_233, Kp_two_of_not_dvd h2]

theorem K2_233_of_two_and_twoHundredThirtyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (233 : ℤ) ∣ h) :
    K2_233 h = (2 : ℚ) * (12487169 / 12487168) := by
  simp [K2_233, Kp_two_of_dvd h2, Kp_twoHundredThirtyThree_of_dvd hp]

theorem K2_233_eq (h : ℤ) :
    K2_233 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (233 : ℤ) ∣ h then (12487169 / 12487168 : ℚ) else (2897022975 / 2897022976 : ℚ)) := by
  simp [K2_233, Kp_two h, Kp_twoHundredThirtyThree h]

end Brockian.Goldbach.WheelK2_233
