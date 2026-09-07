/-
  Brockian/GoldbachWheelK2_499.lean — exact local product K₂·K_499.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_499 from def: 1 ± 1/(p−1)^{3 or 4} with p=499 → (p−1)=498.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_499

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 499) := ⟨by decide⟩

theorem Kp_fourHundredNinetyNine_of_dvd {h : ℤ} (hh : (499 : ℤ) ∣ h) :
    Kp 499 h = (123505993 / 123505992 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNinetyNine_of_not_dvd {h : ℤ} (hh : ¬(499 : ℤ) ∣ h) :
    Kp 499 h = (61505984015 / 61505984016 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNinetyNine (h : ℤ) :
    Kp 499 h = if (499 : ℤ) ∣ h then (123505993 / 123505992 : ℚ) else (61505984015 / 61505984016 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredNinetyNine_of_dvd hh
  · exact Kp_fourHundredNinetyNine_of_not_dvd hh

def K2_499 (h : ℤ) : ℚ := Kp 2 h * Kp 499 h

theorem K2_499_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_499 h = 0 := by
  simp [K2_499, Kp_two_of_not_dvd h2]

theorem K2_499_of_two_and_fourHundredNinetyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (499 : ℤ) ∣ h) :
    K2_499 h = (2 : ℚ) * (123505993 / 123505992) := by
  simp [K2_499, Kp_two_of_dvd h2, Kp_fourHundredNinetyNine_of_dvd hp]

theorem K2_499_eq (h : ℤ) :
    K2_499 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (499 : ℤ) ∣ h then (123505993 / 123505992 : ℚ) else (61505984015 / 61505984016 : ℚ)) := by
  simp [K2_499, Kp_two h, Kp_fourHundredNinetyNine h]

end Brockian.Goldbach.WheelK2_499
