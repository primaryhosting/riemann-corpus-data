/-
  Brockian/GoldbachWheelK2_181.lean — exact local product K₂·K_181.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_181 from def: 1 ± 1/(p−1)^{3 or 4} with p=181 → (p−1)=180.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_181

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 181) := ⟨by decide⟩

theorem Kp_oneHundredEightyOne_of_dvd {h : ℤ} (hh : (181 : ℤ) ∣ h) :
    Kp 181 h = (5832001 / 5832000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredEightyOne_of_not_dvd {h : ℤ} (hh : ¬(181 : ℤ) ∣ h) :
    Kp 181 h = (1049759999 / 1049760000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredEightyOne (h : ℤ) :
    Kp 181 h = if (181 : ℤ) ∣ h then (5832001 / 5832000 : ℚ) else (1049759999 / 1049760000 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredEightyOne_of_dvd hh
  · exact Kp_oneHundredEightyOne_of_not_dvd hh

def K2_181 (h : ℤ) : ℚ := Kp 2 h * Kp 181 h

theorem K2_181_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_181 h = 0 := by
  simp [K2_181, Kp_two_of_not_dvd h2]

theorem K2_181_of_two_and_oneHundredEightyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (181 : ℤ) ∣ h) :
    K2_181 h = (2 : ℚ) * (5832001 / 5832000) := by
  simp [K2_181, Kp_two_of_dvd h2, Kp_oneHundredEightyOne_of_dvd hp]

theorem K2_181_eq (h : ℤ) :
    K2_181 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (181 : ℤ) ∣ h then (5832001 / 5832000 : ℚ) else (1049759999 / 1049760000 : ℚ)) := by
  simp [K2_181, Kp_two h, Kp_oneHundredEightyOne h]

end Brockian.Goldbach.WheelK2_181
