/-
  Brockian/GoldbachWheelK2_769.lean — exact local product K₂·K_769.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_769 from def: 1 ± 1/(p−1)^{3 or 4} with p=769 → (p−1)=768.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_769

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 769) := ⟨by decide⟩

theorem Kp_sevenHundredSixtyNine_of_dvd {h : ℤ} (hh : (769 : ℤ) ∣ h) :
    Kp 769 h = (452984833 / 452984832 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredSixtyNine_of_not_dvd {h : ℤ} (hh : ¬(769 : ℤ) ∣ h) :
    Kp 769 h = (347892350975 / 347892350976 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredSixtyNine (h : ℤ) :
    Kp 769 h = if (769 : ℤ) ∣ h then (452984833 / 452984832 : ℚ) else (347892350975 / 347892350976 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredSixtyNine_of_dvd hh
  · exact Kp_sevenHundredSixtyNine_of_not_dvd hh

def K2_769 (h : ℤ) : ℚ := Kp 2 h * Kp 769 h

theorem K2_769_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_769 h = 0 := by
  simp [K2_769, Kp_two_of_not_dvd h2]

theorem K2_769_of_two_and_sevenHundredSixtyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (769 : ℤ) ∣ h) :
    K2_769 h = (2 : ℚ) * (452984833 / 452984832) := by
  simp [K2_769, Kp_two_of_dvd h2, Kp_sevenHundredSixtyNine_of_dvd hp]

theorem K2_769_eq (h : ℤ) :
    K2_769 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (769 : ℤ) ∣ h then (452984833 / 452984832 : ℚ) else (347892350975 / 347892350976 : ℚ)) := by
  simp [K2_769, Kp_two h, Kp_sevenHundredSixtyNine h]

end Brockian.Goldbach.WheelK2_769
