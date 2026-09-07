/-
  Brockian/GoldbachWheelK2_281.lean — exact local product K₂·K_281.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_281 from def: 1 ± 1/(p−1)^{3 or 4} with p=281 → (p−1)=280.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_281

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 281) := ⟨by decide⟩

theorem Kp_twoHundredEightyOne_of_dvd {h : ℤ} (hh : (281 : ℤ) ∣ h) :
    Kp 281 h = (21952001 / 21952000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredEightyOne_of_not_dvd {h : ℤ} (hh : ¬(281 : ℤ) ∣ h) :
    Kp 281 h = (6146559999 / 6146560000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredEightyOne (h : ℤ) :
    Kp 281 h = if (281 : ℤ) ∣ h then (21952001 / 21952000 : ℚ) else (6146559999 / 6146560000 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredEightyOne_of_dvd hh
  · exact Kp_twoHundredEightyOne_of_not_dvd hh

def K2_281 (h : ℤ) : ℚ := Kp 2 h * Kp 281 h

theorem K2_281_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_281 h = 0 := by
  simp [K2_281, Kp_two_of_not_dvd h2]

theorem K2_281_of_two_and_twoHundredEightyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (281 : ℤ) ∣ h) :
    K2_281 h = (2 : ℚ) * (21952001 / 21952000) := by
  simp [K2_281, Kp_two_of_dvd h2, Kp_twoHundredEightyOne_of_dvd hp]

theorem K2_281_eq (h : ℤ) :
    K2_281 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (281 : ℤ) ∣ h then (21952001 / 21952000 : ℚ) else (6146559999 / 6146560000 : ℚ)) := by
  simp [K2_281, Kp_two h, Kp_twoHundredEightyOne h]

end Brockian.Goldbach.WheelK2_281
