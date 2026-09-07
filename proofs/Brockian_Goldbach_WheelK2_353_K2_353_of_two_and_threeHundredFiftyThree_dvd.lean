/-
  Brockian/GoldbachWheelK2_353.lean — exact local product K₂·K_353.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_353 from def: 1 ± 1/(p−1)^{3 or 4} with p=353 → (p−1)=352.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_353

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 353) := ⟨by decide⟩

theorem Kp_threeHundredFiftyThree_of_dvd {h : ℤ} (hh : (353 : ℤ) ∣ h) :
    Kp 353 h = (43614209 / 43614208 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFiftyThree_of_not_dvd {h : ℤ} (hh : ¬(353 : ℤ) ∣ h) :
    Kp 353 h = (15352201215 / 15352201216 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFiftyThree (h : ℤ) :
    Kp 353 h = if (353 : ℤ) ∣ h then (43614209 / 43614208 : ℚ) else (15352201215 / 15352201216 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredFiftyThree_of_dvd hh
  · exact Kp_threeHundredFiftyThree_of_not_dvd hh

def K2_353 (h : ℤ) : ℚ := Kp 2 h * Kp 353 h

theorem K2_353_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_353 h = 0 := by
  simp [K2_353, Kp_two_of_not_dvd h2]

theorem K2_353_of_two_and_threeHundredFiftyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (353 : ℤ) ∣ h) :
    K2_353 h = (2 : ℚ) * (43614209 / 43614208) := by
  simp [K2_353, Kp_two_of_dvd h2, Kp_threeHundredFiftyThree_of_dvd hp]

theorem K2_353_eq (h : ℤ) :
    K2_353 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (353 : ℤ) ∣ h then (43614209 / 43614208 : ℚ) else (15352201215 / 15352201216 : ℚ)) := by
  simp [K2_353, Kp_two h, Kp_threeHundredFiftyThree h]

end Brockian.Goldbach.WheelK2_353
