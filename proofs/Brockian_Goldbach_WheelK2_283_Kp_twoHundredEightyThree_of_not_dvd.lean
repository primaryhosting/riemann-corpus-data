/-
  Brockian/GoldbachWheelK2_283.lean — exact local product K₂·K_283.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_283 from def: 1 ± 1/(p−1)^{3 or 4} with p=283 → (p−1)=282.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_283

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 283) := ⟨by decide⟩

theorem Kp_twoHundredEightyThree_of_dvd {h : ℤ} (hh : (283 : ℤ) ∣ h) :
    Kp 283 h = (22425769 / 22425768 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredEightyThree_of_not_dvd {h : ℤ} (hh : ¬(283 : ℤ) ∣ h) :
    Kp 283 h = (6324066575 / 6324066576 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredEightyThree (h : ℤ) :
    Kp 283 h = if (283 : ℤ) ∣ h then (22425769 / 22425768 : ℚ) else (6324066575 / 6324066576 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredEightyThree_of_dvd hh
  · exact Kp_twoHundredEightyThree_of_not_dvd hh

def K2_283 (h : ℤ) : ℚ := Kp 2 h * Kp 283 h

theorem K2_283_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_283 h = 0 := by
  simp [K2_283, Kp_two_of_not_dvd h2]

theorem K2_283_of_two_and_twoHundredEightyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (283 : ℤ) ∣ h) :
    K2_283 h = (2 : ℚ) * (22425769 / 22425768) := by
  simp [K2_283, Kp_two_of_dvd h2, Kp_twoHundredEightyThree_of_dvd hp]

theorem K2_283_eq (h : ℤ) :
    K2_283 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (283 : ℤ) ∣ h then (22425769 / 22425768 : ℚ) else (6324066575 / 6324066576 : ℚ)) := by
  simp [K2_283, Kp_two h, Kp_twoHundredEightyThree h]

end Brockian.Goldbach.WheelK2_283
