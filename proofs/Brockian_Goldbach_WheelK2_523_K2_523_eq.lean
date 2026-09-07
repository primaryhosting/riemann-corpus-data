/-
  Brockian/GoldbachWheelK2_523.lean — exact local product K₂·K_523.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_523 from def: 1 ± 1/(p−1)^{3 or 4} with p=523 → (p−1)=522.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_523

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 523) := ⟨by decide⟩

theorem Kp_fiveHundredTwentyThree_of_dvd {h : ℤ} (hh : (523 : ℤ) ∣ h) :
    Kp 523 h = (142236649 / 142236648 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredTwentyThree_of_not_dvd {h : ℤ} (hh : ¬(523 : ℤ) ∣ h) :
    Kp 523 h = (74247530255 / 74247530256 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredTwentyThree (h : ℤ) :
    Kp 523 h = if (523 : ℤ) ∣ h then (142236649 / 142236648 : ℚ) else (74247530255 / 74247530256 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredTwentyThree_of_dvd hh
  · exact Kp_fiveHundredTwentyThree_of_not_dvd hh

def K2_523 (h : ℤ) : ℚ := Kp 2 h * Kp 523 h

theorem K2_523_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_523 h = 0 := by
  simp [K2_523, Kp_two_of_not_dvd h2]

theorem K2_523_of_two_and_fiveHundredTwentyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (523 : ℤ) ∣ h) :
    K2_523 h = (2 : ℚ) * (142236649 / 142236648) := by
  simp [K2_523, Kp_two_of_dvd h2, Kp_fiveHundredTwentyThree_of_dvd hp]

theorem K2_523_eq (h : ℤ) :
    K2_523 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (523 : ℤ) ∣ h then (142236649 / 142236648 : ℚ) else (74247530255 / 74247530256 : ℚ)) := by
  simp [K2_523, Kp_two h, Kp_fiveHundredTwentyThree h]

end Brockian.Goldbach.WheelK2_523
