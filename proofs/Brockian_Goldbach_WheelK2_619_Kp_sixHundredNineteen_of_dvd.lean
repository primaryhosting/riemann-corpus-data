/-
  Brockian/GoldbachWheelK2_619.lean — exact local product K₂·K_619.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_619 from def: 1 ± 1/(p−1)^{3 or 4} with p=619 → (p−1)=618.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_619

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 619) := ⟨by decide⟩

theorem Kp_sixHundredNineteen_of_dvd {h : ℤ} (hh : (619 : ℤ) ∣ h) :
    Kp 619 h = (236029033 / 236029032 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredNineteen_of_not_dvd {h : ℤ} (hh : ¬(619 : ℤ) ∣ h) :
    Kp 619 h = (145865941775 / 145865941776 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredNineteen (h : ℤ) :
    Kp 619 h = if (619 : ℤ) ∣ h then (236029033 / 236029032 : ℚ) else (145865941775 / 145865941776 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredNineteen_of_dvd hh
  · exact Kp_sixHundredNineteen_of_not_dvd hh

def K2_619 (h : ℤ) : ℚ := Kp 2 h * Kp 619 h

theorem K2_619_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_619 h = 0 := by
  simp [K2_619, Kp_two_of_not_dvd h2]

theorem K2_619_of_two_and_sixHundredNineteen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (619 : ℤ) ∣ h) :
    K2_619 h = (2 : ℚ) * (236029033 / 236029032) := by
  simp [K2_619, Kp_two_of_dvd h2, Kp_sixHundredNineteen_of_dvd hp]

theorem K2_619_eq (h : ℤ) :
    K2_619 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (619 : ℤ) ∣ h then (236029033 / 236029032 : ℚ) else (145865941775 / 145865941776 : ℚ)) := by
  simp [K2_619, Kp_two h, Kp_sixHundredNineteen h]

end Brockian.Goldbach.WheelK2_619
