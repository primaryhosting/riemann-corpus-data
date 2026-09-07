/-
  Brockian/GoldbachWheelK2_773.lean — exact local product K₂·K_773.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_773 from def: 1 ± 1/(p−1)^{3 or 4} with p=773 → (p−1)=772.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_773

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 773) := ⟨by decide⟩

theorem Kp_sevenHundredSeventyThree_of_dvd {h : ℤ} (hh : (773 : ℤ) ∣ h) :
    Kp 773 h = (460099649 / 460099648 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredSeventyThree_of_not_dvd {h : ℤ} (hh : ¬(773 : ℤ) ∣ h) :
    Kp 773 h = (355196928255 / 355196928256 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredSeventyThree (h : ℤ) :
    Kp 773 h = if (773 : ℤ) ∣ h then (460099649 / 460099648 : ℚ) else (355196928255 / 355196928256 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredSeventyThree_of_dvd hh
  · exact Kp_sevenHundredSeventyThree_of_not_dvd hh

def K2_773 (h : ℤ) : ℚ := Kp 2 h * Kp 773 h

theorem K2_773_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_773 h = 0 := by
  simp [K2_773, Kp_two_of_not_dvd h2]

theorem K2_773_of_two_and_sevenHundredSeventyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (773 : ℤ) ∣ h) :
    K2_773 h = (2 : ℚ) * (460099649 / 460099648) := by
  simp [K2_773, Kp_two_of_dvd h2, Kp_sevenHundredSeventyThree_of_dvd hp]

theorem K2_773_eq (h : ℤ) :
    K2_773 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (773 : ℤ) ∣ h then (460099649 / 460099648 : ℚ) else (355196928255 / 355196928256 : ℚ)) := by
  simp [K2_773, Kp_two h, Kp_sevenHundredSeventyThree h]

end Brockian.Goldbach.WheelK2_773
