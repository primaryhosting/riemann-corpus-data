/-
  Brockian/GoldbachWheelK2_277.lean — exact local product K₂·K_277.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_277 from def: 1 ± 1/(p−1)^{3 or 4} with p=277 → (p−1)=276.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_277

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 277) := ⟨by decide⟩

theorem Kp_twoHundredSeventySeven_of_dvd {h : ℤ} (hh : (277 : ℤ) ∣ h) :
    Kp 277 h = (21024577 / 21024576 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSeventySeven_of_not_dvd {h : ℤ} (hh : ¬(277 : ℤ) ∣ h) :
    Kp 277 h = (5802782975 / 5802782976 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSeventySeven (h : ℤ) :
    Kp 277 h = if (277 : ℤ) ∣ h then (21024577 / 21024576 : ℚ) else (5802782975 / 5802782976 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredSeventySeven_of_dvd hh
  · exact Kp_twoHundredSeventySeven_of_not_dvd hh

def K2_277 (h : ℤ) : ℚ := Kp 2 h * Kp 277 h

theorem K2_277_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_277 h = 0 := by
  simp [K2_277, Kp_two_of_not_dvd h2]

theorem K2_277_of_two_and_twoHundredSeventySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (277 : ℤ) ∣ h) :
    K2_277 h = (2 : ℚ) * (21024577 / 21024576) := by
  simp [K2_277, Kp_two_of_dvd h2, Kp_twoHundredSeventySeven_of_dvd hp]

theorem K2_277_eq (h : ℤ) :
    K2_277 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (277 : ℤ) ∣ h then (21024577 / 21024576 : ℚ) else (5802782975 / 5802782976 : ℚ)) := by
  simp [K2_277, Kp_two h, Kp_twoHundredSeventySeven h]

end Brockian.Goldbach.WheelK2_277
