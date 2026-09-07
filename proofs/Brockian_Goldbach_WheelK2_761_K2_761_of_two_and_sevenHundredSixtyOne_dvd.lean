/-
  Brockian/GoldbachWheelK2_761.lean — exact local product K₂·K_761.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_761 from def: 1 ± 1/(p−1)^{3 or 4} with p=761 → (p−1)=760.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_761

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 761) := ⟨by decide⟩

theorem Kp_sevenHundredSixtyOne_of_dvd {h : ℤ} (hh : (761 : ℤ) ∣ h) :
    Kp 761 h = (438976001 / 438976000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredSixtyOne_of_not_dvd {h : ℤ} (hh : ¬(761 : ℤ) ∣ h) :
    Kp 761 h = (333621759999 / 333621760000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredSixtyOne (h : ℤ) :
    Kp 761 h = if (761 : ℤ) ∣ h then (438976001 / 438976000 : ℚ) else (333621759999 / 333621760000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredSixtyOne_of_dvd hh
  · exact Kp_sevenHundredSixtyOne_of_not_dvd hh

def K2_761 (h : ℤ) : ℚ := Kp 2 h * Kp 761 h

theorem K2_761_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_761 h = 0 := by
  simp [K2_761, Kp_two_of_not_dvd h2]

theorem K2_761_of_two_and_sevenHundredSixtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (761 : ℤ) ∣ h) :
    K2_761 h = (2 : ℚ) * (438976001 / 438976000) := by
  simp [K2_761, Kp_two_of_dvd h2, Kp_sevenHundredSixtyOne_of_dvd hp]

theorem K2_761_eq (h : ℤ) :
    K2_761 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (761 : ℤ) ∣ h then (438976001 / 438976000 : ℚ) else (333621759999 / 333621760000 : ℚ)) := by
  simp [K2_761, Kp_two h, Kp_sevenHundredSixtyOne h]

end Brockian.Goldbach.WheelK2_761
