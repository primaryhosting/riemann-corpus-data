/-
  Brockian/GoldbachWheelK2_239.lean — exact local product K₂·K_239.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_239 from def: 1 ± 1/(p−1)^{3 or 4} with p=239 → (p−1)=238.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_239

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 239) := ⟨by decide⟩

theorem Kp_twoHundredThirtyNine_of_dvd {h : ℤ} (hh : (239 : ℤ) ∣ h) :
    Kp 239 h = (13481273 / 13481272 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredThirtyNine_of_not_dvd {h : ℤ} (hh : ¬(239 : ℤ) ∣ h) :
    Kp 239 h = (3208542735 / 3208542736 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredThirtyNine (h : ℤ) :
    Kp 239 h = if (239 : ℤ) ∣ h then (13481273 / 13481272 : ℚ) else (3208542735 / 3208542736 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredThirtyNine_of_dvd hh
  · exact Kp_twoHundredThirtyNine_of_not_dvd hh

def K2_239 (h : ℤ) : ℚ := Kp 2 h * Kp 239 h

theorem K2_239_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_239 h = 0 := by
  simp [K2_239, Kp_two_of_not_dvd h2]

theorem K2_239_of_two_and_twoHundredThirtyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (239 : ℤ) ∣ h) :
    K2_239 h = (2 : ℚ) * (13481273 / 13481272) := by
  simp [K2_239, Kp_two_of_dvd h2, Kp_twoHundredThirtyNine_of_dvd hp]

theorem K2_239_eq (h : ℤ) :
    K2_239 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (239 : ℤ) ∣ h then (13481273 / 13481272 : ℚ) else (3208542735 / 3208542736 : ℚ)) := by
  simp [K2_239, Kp_two h, Kp_twoHundredThirtyNine h]

end Brockian.Goldbach.WheelK2_239
