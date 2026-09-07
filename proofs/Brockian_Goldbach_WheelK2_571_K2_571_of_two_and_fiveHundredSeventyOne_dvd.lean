/-
  Brockian/GoldbachWheelK2_571.lean — exact local product K₂·K_571.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_571 from def: 1 ± 1/(p−1)^{3 or 4} with p=571 → (p−1)=570.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_571

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 571) := ⟨by decide⟩

theorem Kp_fiveHundredSeventyOne_of_dvd {h : ℤ} (hh : (571 : ℤ) ∣ h) :
    Kp 571 h = (185193001 / 185193000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredSeventyOne_of_not_dvd {h : ℤ} (hh : ¬(571 : ℤ) ∣ h) :
    Kp 571 h = (105560009999 / 105560010000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredSeventyOne (h : ℤ) :
    Kp 571 h = if (571 : ℤ) ∣ h then (185193001 / 185193000 : ℚ) else (105560009999 / 105560010000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredSeventyOne_of_dvd hh
  · exact Kp_fiveHundredSeventyOne_of_not_dvd hh

def K2_571 (h : ℤ) : ℚ := Kp 2 h * Kp 571 h

theorem K2_571_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_571 h = 0 := by
  simp [K2_571, Kp_two_of_not_dvd h2]

theorem K2_571_of_two_and_fiveHundredSeventyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (571 : ℤ) ∣ h) :
    K2_571 h = (2 : ℚ) * (185193001 / 185193000) := by
  simp [K2_571, Kp_two_of_dvd h2, Kp_fiveHundredSeventyOne_of_dvd hp]

theorem K2_571_eq (h : ℤ) :
    K2_571 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (571 : ℤ) ∣ h then (185193001 / 185193000 : ℚ) else (105560009999 / 105560010000 : ℚ)) := by
  simp [K2_571, Kp_two h, Kp_fiveHundredSeventyOne h]

end Brockian.Goldbach.WheelK2_571
