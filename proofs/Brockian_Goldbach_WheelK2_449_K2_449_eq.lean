/-
  Brockian/GoldbachWheelK2_449.lean — exact local product K₂·K_449.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_449 from def: 1 ± 1/(p−1)^{3 or 4} with p=449 → (p−1)=448.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_449

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 449) := ⟨by decide⟩

theorem Kp_fourHundredFortyNine_of_dvd {h : ℤ} (hh : (449 : ℤ) ∣ h) :
    Kp 449 h = (89915393 / 89915392 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredFortyNine_of_not_dvd {h : ℤ} (hh : ¬(449 : ℤ) ∣ h) :
    Kp 449 h = (40282095615 / 40282095616 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredFortyNine (h : ℤ) :
    Kp 449 h = if (449 : ℤ) ∣ h then (89915393 / 89915392 : ℚ) else (40282095615 / 40282095616 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredFortyNine_of_dvd hh
  · exact Kp_fourHundredFortyNine_of_not_dvd hh

def K2_449 (h : ℤ) : ℚ := Kp 2 h * Kp 449 h

theorem K2_449_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_449 h = 0 := by
  simp [K2_449, Kp_two_of_not_dvd h2]

theorem K2_449_of_two_and_fourHundredFortyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (449 : ℤ) ∣ h) :
    K2_449 h = (2 : ℚ) * (89915393 / 89915392) := by
  simp [K2_449, Kp_two_of_dvd h2, Kp_fourHundredFortyNine_of_dvd hp]

theorem K2_449_eq (h : ℤ) :
    K2_449 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (449 : ℤ) ∣ h then (89915393 / 89915392 : ℚ) else (40282095615 / 40282095616 : ℚ)) := by
  simp [K2_449, Kp_two h, Kp_fourHundredFortyNine h]

end Brockian.Goldbach.WheelK2_449
