/-
  Brockian/GoldbachWheelK2_607.lean — exact local product K₂·K_607.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_607 from def: 1 ± 1/(p−1)^{3 or 4} with p=607 → (p−1)=606.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_607

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 607) := ⟨by decide⟩

theorem Kp_sixHundredSeven_of_dvd {h : ℤ} (hh : (607 : ℤ) ∣ h) :
    Kp 607 h = (222545017 / 222545016 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeven_of_not_dvd {h : ℤ} (hh : ¬(607 : ℤ) ∣ h) :
    Kp 607 h = (134862279695 / 134862279696 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeven (h : ℤ) :
    Kp 607 h = if (607 : ℤ) ∣ h then (222545017 / 222545016 : ℚ) else (134862279695 / 134862279696 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredSeven_of_dvd hh
  · exact Kp_sixHundredSeven_of_not_dvd hh

def K2_607 (h : ℤ) : ℚ := Kp 2 h * Kp 607 h

theorem K2_607_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_607 h = 0 := by
  simp [K2_607, Kp_two_of_not_dvd h2]

theorem K2_607_of_two_and_sixHundredSeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (607 : ℤ) ∣ h) :
    K2_607 h = (2 : ℚ) * (222545017 / 222545016) := by
  simp [K2_607, Kp_two_of_dvd h2, Kp_sixHundredSeven_of_dvd hp]

theorem K2_607_eq (h : ℤ) :
    K2_607 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (607 : ℤ) ∣ h then (222545017 / 222545016 : ℚ) else (134862279695 / 134862279696 : ℚ)) := by
  simp [K2_607, Kp_two h, Kp_sixHundredSeven h]

end Brockian.Goldbach.WheelK2_607
