/-
  Brockian/GoldbachWheelK2_293.lean — exact local product K₂·K_293.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_293 from def: 1 ± 1/(p−1)^{3 or 4} with p=293 → (p−1)=292.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_293

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 293) := ⟨by decide⟩

theorem Kp_twoHundredNinetyThree_of_dvd {h : ℤ} (hh : (293 : ℤ) ∣ h) :
    Kp 293 h = (24897089 / 24897088 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredNinetyThree_of_not_dvd {h : ℤ} (hh : ¬(293 : ℤ) ∣ h) :
    Kp 293 h = (7269949695 / 7269949696 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredNinetyThree (h : ℤ) :
    Kp 293 h = if (293 : ℤ) ∣ h then (24897089 / 24897088 : ℚ) else (7269949695 / 7269949696 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredNinetyThree_of_dvd hh
  · exact Kp_twoHundredNinetyThree_of_not_dvd hh

def K2_293 (h : ℤ) : ℚ := Kp 2 h * Kp 293 h

theorem K2_293_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_293 h = 0 := by
  simp [K2_293, Kp_two_of_not_dvd h2]

theorem K2_293_of_two_and_twoHundredNinetyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (293 : ℤ) ∣ h) :
    K2_293 h = (2 : ℚ) * (24897089 / 24897088) := by
  simp [K2_293, Kp_two_of_dvd h2, Kp_twoHundredNinetyThree_of_dvd hp]

theorem K2_293_eq (h : ℤ) :
    K2_293 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (293 : ℤ) ∣ h then (24897089 / 24897088 : ℚ) else (7269949695 / 7269949696 : ℚ)) := by
  simp [K2_293, Kp_two h, Kp_twoHundredNinetyThree h]

end Brockian.Goldbach.WheelK2_293
