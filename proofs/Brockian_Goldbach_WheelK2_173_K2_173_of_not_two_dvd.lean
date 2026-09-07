/-
  Brockian/GoldbachWheelK2_173.lean — exact local product K₂·K_173.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_173 from def: 1 ± 1/(p−1)^{3 or 4} with p=173 → (p−1)=172.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_173

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 173) := ⟨by decide⟩

theorem Kp_oneHundredSeventyThree_of_dvd {h : ℤ} (hh : (173 : ℤ) ∣ h) :
    Kp 173 h = (5088449 / 5088448 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSeventyThree_of_not_dvd {h : ℤ} (hh : ¬(173 : ℤ) ∣ h) :
    Kp 173 h = (875213055 / 875213056 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSeventyThree (h : ℤ) :
    Kp 173 h = if (173 : ℤ) ∣ h then (5088449 / 5088448 : ℚ) else (875213055 / 875213056 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredSeventyThree_of_dvd hh
  · exact Kp_oneHundredSeventyThree_of_not_dvd hh

def K2_173 (h : ℤ) : ℚ := Kp 2 h * Kp 173 h

theorem K2_173_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_173 h = 0 := by
  simp [K2_173, Kp_two_of_not_dvd h2]

theorem K2_173_of_two_and_oneHundredSeventyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (173 : ℤ) ∣ h) :
    K2_173 h = (2 : ℚ) * (5088449 / 5088448) := by
  simp [K2_173, Kp_two_of_dvd h2, Kp_oneHundredSeventyThree_of_dvd hp]

theorem K2_173_eq (h : ℤ) :
    K2_173 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (173 : ℤ) ∣ h then (5088449 / 5088448 : ℚ) else (875213055 / 875213056 : ℚ)) := by
  simp [K2_173, Kp_two h, Kp_oneHundredSeventyThree h]

end Brockian.Goldbach.WheelK2_173
