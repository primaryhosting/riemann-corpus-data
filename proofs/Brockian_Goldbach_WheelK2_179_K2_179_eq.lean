/-
  Brockian/GoldbachWheelK2_179.lean — exact local product K₂·K_179.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_179 from def: 1 ± 1/(p−1)^{3 or 4} with p=179 → (p−1)=178.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_179

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 179) := ⟨by decide⟩

theorem Kp_oneHundredSeventyNine_of_dvd {h : ℤ} (hh : (179 : ℤ) ∣ h) :
    Kp 179 h = (5639753 / 5639752 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSeventyNine_of_not_dvd {h : ℤ} (hh : ¬(179 : ℤ) ∣ h) :
    Kp 179 h = (1003875855 / 1003875856 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSeventyNine (h : ℤ) :
    Kp 179 h = if (179 : ℤ) ∣ h then (5639753 / 5639752 : ℚ) else (1003875855 / 1003875856 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredSeventyNine_of_dvd hh
  · exact Kp_oneHundredSeventyNine_of_not_dvd hh

def K2_179 (h : ℤ) : ℚ := Kp 2 h * Kp 179 h

theorem K2_179_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_179 h = 0 := by
  simp [K2_179, Kp_two_of_not_dvd h2]

theorem K2_179_of_two_and_oneHundredSeventyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (179 : ℤ) ∣ h) :
    K2_179 h = (2 : ℚ) * (5639753 / 5639752) := by
  simp [K2_179, Kp_two_of_dvd h2, Kp_oneHundredSeventyNine_of_dvd hp]

theorem K2_179_eq (h : ℤ) :
    K2_179 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (179 : ℤ) ∣ h then (5639753 / 5639752 : ℚ) else (1003875855 / 1003875856 : ℚ)) := by
  simp [K2_179, Kp_two h, Kp_oneHundredSeventyNine h]

end Brockian.Goldbach.WheelK2_179
