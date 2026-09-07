/-
  Brockian/GoldbachWheelK2_383.lean — exact local product K₂·K_383.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_383 from def: 1 ± 1/(p−1)^{3 or 4} with p=383 → (p−1)=382.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_383

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 383) := ⟨by decide⟩

theorem Kp_threeHundredEightyThree_of_dvd {h : ℤ} (hh : (383 : ℤ) ∣ h) :
    Kp 383 h = (55742969 / 55742968 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredEightyThree_of_not_dvd {h : ℤ} (hh : ¬(383 : ℤ) ∣ h) :
    Kp 383 h = (21293813775 / 21293813776 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredEightyThree (h : ℤ) :
    Kp 383 h = if (383 : ℤ) ∣ h then (55742969 / 55742968 : ℚ) else (21293813775 / 21293813776 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredEightyThree_of_dvd hh
  · exact Kp_threeHundredEightyThree_of_not_dvd hh

def K2_383 (h : ℤ) : ℚ := Kp 2 h * Kp 383 h

theorem K2_383_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_383 h = 0 := by
  simp [K2_383, Kp_two_of_not_dvd h2]

theorem K2_383_of_two_and_threeHundredEightyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (383 : ℤ) ∣ h) :
    K2_383 h = (2 : ℚ) * (55742969 / 55742968) := by
  simp [K2_383, Kp_two_of_dvd h2, Kp_threeHundredEightyThree_of_dvd hp]

theorem K2_383_eq (h : ℤ) :
    K2_383 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (383 : ℤ) ∣ h then (55742969 / 55742968 : ℚ) else (21293813775 / 21293813776 : ℚ)) := by
  simp [K2_383, Kp_two h, Kp_threeHundredEightyThree h]

end Brockian.Goldbach.WheelK2_383
