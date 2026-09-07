/-
  Brockian/GoldbachWheelK2_317.lean — exact local product K₂·K_317.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_317 from def: 1 ± 1/(p−1)^{3 or 4} with p=317 → (p−1)=316.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_317

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 317) := ⟨by decide⟩

theorem Kp_threeHundredSeventeen_of_dvd {h : ℤ} (hh : (317 : ℤ) ∣ h) :
    Kp 317 h = (31554497 / 31554496 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeventeen_of_not_dvd {h : ℤ} (hh : ¬(317 : ℤ) ∣ h) :
    Kp 317 h = (9971220735 / 9971220736 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeventeen (h : ℤ) :
    Kp 317 h = if (317 : ℤ) ∣ h then (31554497 / 31554496 : ℚ) else (9971220735 / 9971220736 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredSeventeen_of_dvd hh
  · exact Kp_threeHundredSeventeen_of_not_dvd hh

def K2_317 (h : ℤ) : ℚ := Kp 2 h * Kp 317 h

theorem K2_317_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_317 h = 0 := by
  simp [K2_317, Kp_two_of_not_dvd h2]

theorem K2_317_of_two_and_threeHundredSeventeen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (317 : ℤ) ∣ h) :
    K2_317 h = (2 : ℚ) * (31554497 / 31554496) := by
  simp [K2_317, Kp_two_of_dvd h2, Kp_threeHundredSeventeen_of_dvd hp]

theorem K2_317_eq (h : ℤ) :
    K2_317 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (317 : ℤ) ∣ h then (31554497 / 31554496 : ℚ) else (9971220735 / 9971220736 : ℚ)) := by
  simp [K2_317, Kp_two h, Kp_threeHundredSeventeen h]

end Brockian.Goldbach.WheelK2_317
