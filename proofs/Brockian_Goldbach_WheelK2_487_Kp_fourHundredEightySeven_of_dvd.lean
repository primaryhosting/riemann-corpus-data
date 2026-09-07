/-
  Brockian/GoldbachWheelK2_487.lean — exact local product K₂·K_487.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_487 from def: 1 ± 1/(p−1)^{3 or 4} with p=487 → (p−1)=486.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_487

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 487) := ⟨by decide⟩

theorem Kp_fourHundredEightySeven_of_dvd {h : ℤ} (hh : (487 : ℤ) ∣ h) :
    Kp 487 h = (114791257 / 114791256 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredEightySeven_of_not_dvd {h : ℤ} (hh : ¬(487 : ℤ) ∣ h) :
    Kp 487 h = (55788550415 / 55788550416 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredEightySeven (h : ℤ) :
    Kp 487 h = if (487 : ℤ) ∣ h then (114791257 / 114791256 : ℚ) else (55788550415 / 55788550416 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredEightySeven_of_dvd hh
  · exact Kp_fourHundredEightySeven_of_not_dvd hh

def K2_487 (h : ℤ) : ℚ := Kp 2 h * Kp 487 h

theorem K2_487_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_487 h = 0 := by
  simp [K2_487, Kp_two_of_not_dvd h2]

theorem K2_487_of_two_and_fourHundredEightySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (487 : ℤ) ∣ h) :
    K2_487 h = (2 : ℚ) * (114791257 / 114791256) := by
  simp [K2_487, Kp_two_of_dvd h2, Kp_fourHundredEightySeven_of_dvd hp]

theorem K2_487_eq (h : ℤ) :
    K2_487 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (487 : ℤ) ∣ h then (114791257 / 114791256 : ℚ) else (55788550415 / 55788550416 : ℚ)) := by
  simp [K2_487, Kp_two h, Kp_fourHundredEightySeven h]

end Brockian.Goldbach.WheelK2_487
