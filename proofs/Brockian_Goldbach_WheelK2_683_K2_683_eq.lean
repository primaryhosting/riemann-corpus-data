/-
  Brockian/GoldbachWheelK2_683.lean — exact local product K₂·K_683.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_683 from def: 1 ± 1/(p−1)^{3 or 4} with p=683 → (p−1)=682.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_683

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 683) := ⟨by decide⟩

theorem Kp_sixHundredEightyThree_of_dvd {h : ℤ} (hh : (683 : ℤ) ∣ h) :
    Kp 683 h = (317214569 / 317214568 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredEightyThree_of_not_dvd {h : ℤ} (hh : ¬(683 : ℤ) ∣ h) :
    Kp 683 h = (216340335375 / 216340335376 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredEightyThree (h : ℤ) :
    Kp 683 h = if (683 : ℤ) ∣ h then (317214569 / 317214568 : ℚ) else (216340335375 / 216340335376 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredEightyThree_of_dvd hh
  · exact Kp_sixHundredEightyThree_of_not_dvd hh

def K2_683 (h : ℤ) : ℚ := Kp 2 h * Kp 683 h

theorem K2_683_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_683 h = 0 := by
  simp [K2_683, Kp_two_of_not_dvd h2]

theorem K2_683_of_two_and_sixHundredEightyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (683 : ℤ) ∣ h) :
    K2_683 h = (2 : ℚ) * (317214569 / 317214568) := by
  simp [K2_683, Kp_two_of_dvd h2, Kp_sixHundredEightyThree_of_dvd hp]

theorem K2_683_eq (h : ℤ) :
    K2_683 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (683 : ℤ) ∣ h then (317214569 / 317214568 : ℚ) else (216340335375 / 216340335376 : ℚ)) := by
  simp [K2_683, Kp_two h, Kp_sixHundredEightyThree h]

end Brockian.Goldbach.WheelK2_683
