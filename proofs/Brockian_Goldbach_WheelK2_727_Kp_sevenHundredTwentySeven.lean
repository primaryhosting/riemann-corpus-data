/-
  Brockian/GoldbachWheelK2_727.lean — exact local product K₂·K_727.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_727 from def: 1 ± 1/(p−1)^{3 or 4} with p=727 → (p−1)=726.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_727

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 727) := ⟨by decide⟩

theorem Kp_sevenHundredTwentySeven_of_dvd {h : ℤ} (hh : (727 : ℤ) ∣ h) :
    Kp 727 h = (382657177 / 382657176 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredTwentySeven_of_not_dvd {h : ℤ} (hh : ¬(727 : ℤ) ∣ h) :
    Kp 727 h = (277809109775 / 277809109776 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredTwentySeven (h : ℤ) :
    Kp 727 h = if (727 : ℤ) ∣ h then (382657177 / 382657176 : ℚ) else (277809109775 / 277809109776 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredTwentySeven_of_dvd hh
  · exact Kp_sevenHundredTwentySeven_of_not_dvd hh

def K2_727 (h : ℤ) : ℚ := Kp 2 h * Kp 727 h

theorem K2_727_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_727 h = 0 := by
  simp [K2_727, Kp_two_of_not_dvd h2]

theorem K2_727_of_two_and_sevenHundredTwentySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (727 : ℤ) ∣ h) :
    K2_727 h = (2 : ℚ) * (382657177 / 382657176) := by
  simp [K2_727, Kp_two_of_dvd h2, Kp_sevenHundredTwentySeven_of_dvd hp]

theorem K2_727_eq (h : ℤ) :
    K2_727 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (727 : ℤ) ∣ h then (382657177 / 382657176 : ℚ) else (277809109775 / 277809109776 : ℚ)) := by
  simp [K2_727, Kp_two h, Kp_sevenHundredTwentySeven h]

end Brockian.Goldbach.WheelK2_727
