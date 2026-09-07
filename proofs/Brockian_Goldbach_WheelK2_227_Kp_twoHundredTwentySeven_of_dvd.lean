/-
  Brockian/GoldbachWheelK2_227.lean — exact local product K₂·K_227.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_227 from def: 1 ± 1/(p−1)^{3 or 4} with p=227 → (p−1)=226.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_227

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 227) := ⟨by decide⟩

theorem Kp_twoHundredTwentySeven_of_dvd {h : ℤ} (hh : (227 : ℤ) ∣ h) :
    Kp 227 h = (11543177 / 11543176 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredTwentySeven_of_not_dvd {h : ℤ} (hh : ¬(227 : ℤ) ∣ h) :
    Kp 227 h = (2608757775 / 2608757776 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredTwentySeven (h : ℤ) :
    Kp 227 h = if (227 : ℤ) ∣ h then (11543177 / 11543176 : ℚ) else (2608757775 / 2608757776 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredTwentySeven_of_dvd hh
  · exact Kp_twoHundredTwentySeven_of_not_dvd hh

def K2_227 (h : ℤ) : ℚ := Kp 2 h * Kp 227 h

theorem K2_227_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_227 h = 0 := by
  simp [K2_227, Kp_two_of_not_dvd h2]

theorem K2_227_of_two_and_twoHundredTwentySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (227 : ℤ) ∣ h) :
    K2_227 h = (2 : ℚ) * (11543177 / 11543176) := by
  simp [K2_227, Kp_two_of_dvd h2, Kp_twoHundredTwentySeven_of_dvd hp]

theorem K2_227_eq (h : ℤ) :
    K2_227 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (227 : ℤ) ∣ h then (11543177 / 11543176 : ℚ) else (2608757775 / 2608757776 : ℚ)) := by
  simp [K2_227, Kp_two h, Kp_twoHundredTwentySeven h]

end Brockian.Goldbach.WheelK2_227
