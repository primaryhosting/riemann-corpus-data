/-
  Brockian/GoldbachWheelK2_491.lean — exact local product K₂·K_491.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_491 from def: 1 ± 1/(p−1)^{3 or 4} with p=491 → (p−1)=490.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_491

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 491) := ⟨by decide⟩

theorem Kp_fourHundredNinetyOne_of_dvd {h : ℤ} (hh : (491 : ℤ) ∣ h) :
    Kp 491 h = (117649001 / 117649000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNinetyOne_of_not_dvd {h : ℤ} (hh : ¬(491 : ℤ) ∣ h) :
    Kp 491 h = (57648009999 / 57648010000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNinetyOne (h : ℤ) :
    Kp 491 h = if (491 : ℤ) ∣ h then (117649001 / 117649000 : ℚ) else (57648009999 / 57648010000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredNinetyOne_of_dvd hh
  · exact Kp_fourHundredNinetyOne_of_not_dvd hh

def K2_491 (h : ℤ) : ℚ := Kp 2 h * Kp 491 h

theorem K2_491_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_491 h = 0 := by
  simp [K2_491, Kp_two_of_not_dvd h2]

theorem K2_491_of_two_and_fourHundredNinetyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (491 : ℤ) ∣ h) :
    K2_491 h = (2 : ℚ) * (117649001 / 117649000) := by
  simp [K2_491, Kp_two_of_dvd h2, Kp_fourHundredNinetyOne_of_dvd hp]

theorem K2_491_eq (h : ℤ) :
    K2_491 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (491 : ℤ) ∣ h then (117649001 / 117649000 : ℚ) else (57648009999 / 57648010000 : ℚ)) := by
  simp [K2_491, Kp_two h, Kp_fourHundredNinetyOne h]

end Brockian.Goldbach.WheelK2_491
