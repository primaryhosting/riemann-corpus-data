/-
  Brockian/GoldbachWheelK2_349.lean — exact local product K₂·K_349.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_349 from def: 1 ± 1/(p−1)^{3 or 4} with p=349 → (p−1)=348.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_349

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 349) := ⟨by decide⟩

theorem Kp_threeHundredFortyNine_of_dvd {h : ℤ} (hh : (349 : ℤ) ∣ h) :
    Kp 349 h = (42144193 / 42144192 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFortyNine_of_not_dvd {h : ℤ} (hh : ¬(349 : ℤ) ∣ h) :
    Kp 349 h = (14666178815 / 14666178816 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFortyNine (h : ℤ) :
    Kp 349 h = if (349 : ℤ) ∣ h then (42144193 / 42144192 : ℚ) else (14666178815 / 14666178816 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredFortyNine_of_dvd hh
  · exact Kp_threeHundredFortyNine_of_not_dvd hh

def K2_349 (h : ℤ) : ℚ := Kp 2 h * Kp 349 h

theorem K2_349_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_349 h = 0 := by
  simp [K2_349, Kp_two_of_not_dvd h2]

theorem K2_349_of_two_and_threeHundredFortyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (349 : ℤ) ∣ h) :
    K2_349 h = (2 : ℚ) * (42144193 / 42144192) := by
  simp [K2_349, Kp_two_of_dvd h2, Kp_threeHundredFortyNine_of_dvd hp]

theorem K2_349_eq (h : ℤ) :
    K2_349 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (349 : ℤ) ∣ h then (42144193 / 42144192 : ℚ) else (14666178815 / 14666178816 : ℚ)) := by
  simp [K2_349, Kp_two h, Kp_threeHundredFortyNine h]

end Brockian.Goldbach.WheelK2_349
