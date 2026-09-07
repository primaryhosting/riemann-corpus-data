/-
  Brockian/GoldbachWheelK2_211.lean — exact local product K₂·K_211.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_211 from def: 1 ± 1/(p−1)^{3 or 4} with p=211 → (p−1)=210.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_211

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 211) := ⟨by decide⟩

theorem Kp_twoHundredEleven_of_dvd {h : ℤ} (hh : (211 : ℤ) ∣ h) :
    Kp 211 h = (9261001 / 9261000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredEleven_of_not_dvd {h : ℤ} (hh : ¬(211 : ℤ) ∣ h) :
    Kp 211 h = (1944809999 / 1944810000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredEleven (h : ℤ) :
    Kp 211 h = if (211 : ℤ) ∣ h then (9261001 / 9261000 : ℚ) else (1944809999 / 1944810000 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredEleven_of_dvd hh
  · exact Kp_twoHundredEleven_of_not_dvd hh

def K2_211 (h : ℤ) : ℚ := Kp 2 h * Kp 211 h

theorem K2_211_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_211 h = 0 := by
  simp [K2_211, Kp_two_of_not_dvd h2]

theorem K2_211_of_two_and_twoHundredEleven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (211 : ℤ) ∣ h) :
    K2_211 h = (2 : ℚ) * (9261001 / 9261000) := by
  simp [K2_211, Kp_two_of_dvd h2, Kp_twoHundredEleven_of_dvd hp]

theorem K2_211_eq (h : ℤ) :
    K2_211 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (211 : ℤ) ∣ h then (9261001 / 9261000 : ℚ) else (1944809999 / 1944810000 : ℚ)) := by
  simp [K2_211, Kp_two h, Kp_twoHundredEleven h]

end Brockian.Goldbach.WheelK2_211
