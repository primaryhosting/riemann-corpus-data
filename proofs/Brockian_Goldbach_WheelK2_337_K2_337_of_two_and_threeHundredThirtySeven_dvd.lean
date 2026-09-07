/-
  Brockian/GoldbachWheelK2_337.lean — exact local product K₂·K_337.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_337 from def: 1 ± 1/(p−1)^{3 or 4} with p=337 → (p−1)=336.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_337

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 337) := ⟨by decide⟩

theorem Kp_threeHundredThirtySeven_of_dvd {h : ℤ} (hh : (337 : ℤ) ∣ h) :
    Kp 337 h = (37933057 / 37933056 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredThirtySeven_of_not_dvd {h : ℤ} (hh : ¬(337 : ℤ) ∣ h) :
    Kp 337 h = (12745506815 / 12745506816 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredThirtySeven (h : ℤ) :
    Kp 337 h = if (337 : ℤ) ∣ h then (37933057 / 37933056 : ℚ) else (12745506815 / 12745506816 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredThirtySeven_of_dvd hh
  · exact Kp_threeHundredThirtySeven_of_not_dvd hh

def K2_337 (h : ℤ) : ℚ := Kp 2 h * Kp 337 h

theorem K2_337_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_337 h = 0 := by
  simp [K2_337, Kp_two_of_not_dvd h2]

theorem K2_337_of_two_and_threeHundredThirtySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (337 : ℤ) ∣ h) :
    K2_337 h = (2 : ℚ) * (37933057 / 37933056) := by
  simp [K2_337, Kp_two_of_dvd h2, Kp_threeHundredThirtySeven_of_dvd hp]

theorem K2_337_eq (h : ℤ) :
    K2_337 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (337 : ℤ) ∣ h then (37933057 / 37933056 : ℚ) else (12745506815 / 12745506816 : ℚ)) := by
  simp [K2_337, Kp_two h, Kp_threeHundredThirtySeven h]

end Brockian.Goldbach.WheelK2_337
