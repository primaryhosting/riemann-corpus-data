/-
  Brockian/GoldbachWheelK2_389.lean — exact local product K₂·K_389.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_389 from def: 1 ± 1/(p−1)^{3 or 4} with p=389 → (p−1)=388.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_389

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 389) := ⟨by decide⟩

theorem Kp_threeHundredEightyNine_of_dvd {h : ℤ} (hh : (389 : ℤ) ∣ h) :
    Kp 389 h = (58411073 / 58411072 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredEightyNine_of_not_dvd {h : ℤ} (hh : ¬(389 : ℤ) ∣ h) :
    Kp 389 h = (22663495935 / 22663495936 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredEightyNine (h : ℤ) :
    Kp 389 h = if (389 : ℤ) ∣ h then (58411073 / 58411072 : ℚ) else (22663495935 / 22663495936 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredEightyNine_of_dvd hh
  · exact Kp_threeHundredEightyNine_of_not_dvd hh

def K2_389 (h : ℤ) : ℚ := Kp 2 h * Kp 389 h

theorem K2_389_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_389 h = 0 := by
  simp [K2_389, Kp_two_of_not_dvd h2]

theorem K2_389_of_two_and_threeHundredEightyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (389 : ℤ) ∣ h) :
    K2_389 h = (2 : ℚ) * (58411073 / 58411072) := by
  simp [K2_389, Kp_two_of_dvd h2, Kp_threeHundredEightyNine_of_dvd hp]

theorem K2_389_eq (h : ℤ) :
    K2_389 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (389 : ℤ) ∣ h then (58411073 / 58411072 : ℚ) else (22663495935 / 22663495936 : ℚ)) := by
  simp [K2_389, Kp_two h, Kp_threeHundredEightyNine h]

end Brockian.Goldbach.WheelK2_389
