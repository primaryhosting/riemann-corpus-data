/-
  Brockian/GoldbachWheelK2_401.lean — exact local product K₂·K_401.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_401 from def: 1 ± 1/(p−1)^{3 or 4} with p=401 → (p−1)=400.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_401

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 401) := ⟨by decide⟩

theorem Kp_fourHundredOne_of_dvd {h : ℤ} (hh : (401 : ℤ) ∣ h) :
    Kp 401 h = (64000001 / 64000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredOne_of_not_dvd {h : ℤ} (hh : ¬(401 : ℤ) ∣ h) :
    Kp 401 h = (25599999999 / 25600000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredOne (h : ℤ) :
    Kp 401 h = if (401 : ℤ) ∣ h then (64000001 / 64000000 : ℚ) else (25599999999 / 25600000000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredOne_of_dvd hh
  · exact Kp_fourHundredOne_of_not_dvd hh

def K2_401 (h : ℤ) : ℚ := Kp 2 h * Kp 401 h

theorem K2_401_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_401 h = 0 := by
  simp [K2_401, Kp_two_of_not_dvd h2]

theorem K2_401_of_two_and_fourHundredOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (401 : ℤ) ∣ h) :
    K2_401 h = (2 : ℚ) * (64000001 / 64000000) := by
  simp [K2_401, Kp_two_of_dvd h2, Kp_fourHundredOne_of_dvd hp]

theorem K2_401_eq (h : ℤ) :
    K2_401 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (401 : ℤ) ∣ h then (64000001 / 64000000 : ℚ) else (25599999999 / 25600000000 : ℚ)) := by
  simp [K2_401, Kp_two h, Kp_fourHundredOne h]

end Brockian.Goldbach.WheelK2_401
