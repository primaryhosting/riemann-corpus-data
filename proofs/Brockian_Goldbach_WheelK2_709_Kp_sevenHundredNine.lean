/-
  Brockian/GoldbachWheelK2_709.lean — exact local product K₂·K_709.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_709 from def: 1 ± 1/(p−1)^{3 or 4} with p=709 → (p−1)=708.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_709

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 709) := ⟨by decide⟩

theorem Kp_sevenHundredNine_of_dvd {h : ℤ} (hh : (709 : ℤ) ∣ h) :
    Kp 709 h = (354894913 / 354894912 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredNine_of_not_dvd {h : ℤ} (hh : ¬(709 : ℤ) ∣ h) :
    Kp 709 h = (251265597695 / 251265597696 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredNine (h : ℤ) :
    Kp 709 h = if (709 : ℤ) ∣ h then (354894913 / 354894912 : ℚ) else (251265597695 / 251265597696 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredNine_of_dvd hh
  · exact Kp_sevenHundredNine_of_not_dvd hh

def K2_709 (h : ℤ) : ℚ := Kp 2 h * Kp 709 h

theorem K2_709_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_709 h = 0 := by
  simp [K2_709, Kp_two_of_not_dvd h2]

theorem K2_709_of_two_and_sevenHundredNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (709 : ℤ) ∣ h) :
    K2_709 h = (2 : ℚ) * (354894913 / 354894912) := by
  simp [K2_709, Kp_two_of_dvd h2, Kp_sevenHundredNine_of_dvd hp]

theorem K2_709_eq (h : ℤ) :
    K2_709 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (709 : ℤ) ∣ h then (354894913 / 354894912 : ℚ) else (251265597695 / 251265597696 : ℚ)) := by
  simp [K2_709, Kp_two h, Kp_sevenHundredNine h]

end Brockian.Goldbach.WheelK2_709
