/-
  Brockian/GoldbachWheelK2_787.lean — exact local product K₂·K_787.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_787 from def: 1 ± 1/(p−1)^{3 or 4} with p=787 → (p−1)=786.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_787

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 787) := ⟨by decide⟩

theorem Kp_sevenHundredEightySeven_of_dvd {h : ℤ} (hh : (787 : ℤ) ∣ h) :
    Kp 787 h = (485587657 / 485587656 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredEightySeven_of_not_dvd {h : ℤ} (hh : ¬(787 : ℤ) ∣ h) :
    Kp 787 h = (381671897615 / 381671897616 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredEightySeven (h : ℤ) :
    Kp 787 h = if (787 : ℤ) ∣ h then (485587657 / 485587656 : ℚ) else (381671897615 / 381671897616 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredEightySeven_of_dvd hh
  · exact Kp_sevenHundredEightySeven_of_not_dvd hh

def K2_787 (h : ℤ) : ℚ := Kp 2 h * Kp 787 h

theorem K2_787_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_787 h = 0 := by
  simp [K2_787, Kp_two_of_not_dvd h2]

theorem K2_787_of_two_and_sevenHundredEightySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (787 : ℤ) ∣ h) :
    K2_787 h = (2 : ℚ) * (485587657 / 485587656) := by
  simp [K2_787, Kp_two_of_dvd h2, Kp_sevenHundredEightySeven_of_dvd hp]

theorem K2_787_eq (h : ℤ) :
    K2_787 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (787 : ℤ) ∣ h then (485587657 / 485587656 : ℚ) else (381671897615 / 381671897616 : ℚ)) := by
  simp [K2_787, Kp_two h, Kp_sevenHundredEightySeven h]

end Brockian.Goldbach.WheelK2_787
