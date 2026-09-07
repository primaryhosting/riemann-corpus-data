/-
  Brockian/GoldbachWheelK2_479.lean — exact local product K₂·K_479.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_479 from def: 1 ± 1/(p−1)^{3 or 4} with p=479 → (p−1)=478.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_479

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 479) := ⟨by decide⟩

theorem Kp_fourHundredSeventyNine_of_dvd {h : ℤ} (hh : (479 : ℤ) ∣ h) :
    Kp 479 h = (109215353 / 109215352 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSeventyNine_of_not_dvd {h : ℤ} (hh : ¬(479 : ℤ) ∣ h) :
    Kp 479 h = (52204938255 / 52204938256 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredSeventyNine (h : ℤ) :
    Kp 479 h = if (479 : ℤ) ∣ h then (109215353 / 109215352 : ℚ) else (52204938255 / 52204938256 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredSeventyNine_of_dvd hh
  · exact Kp_fourHundredSeventyNine_of_not_dvd hh

def K2_479 (h : ℤ) : ℚ := Kp 2 h * Kp 479 h

theorem K2_479_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_479 h = 0 := by
  simp [K2_479, Kp_two_of_not_dvd h2]

theorem K2_479_of_two_and_fourHundredSeventyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (479 : ℤ) ∣ h) :
    K2_479 h = (2 : ℚ) * (109215353 / 109215352) := by
  simp [K2_479, Kp_two_of_dvd h2, Kp_fourHundredSeventyNine_of_dvd hp]

theorem K2_479_eq (h : ℤ) :
    K2_479 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (479 : ℤ) ∣ h then (109215353 / 109215352 : ℚ) else (52204938255 / 52204938256 : ℚ)) := by
  simp [K2_479, Kp_two h, Kp_fourHundredSeventyNine h]

end Brockian.Goldbach.WheelK2_479
