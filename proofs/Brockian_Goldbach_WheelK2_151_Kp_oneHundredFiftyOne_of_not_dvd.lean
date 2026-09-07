/-
  Brockian/GoldbachWheelK2_151.lean — exact local product K₂·K_151.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_151 from def: 1 ± 1/(p−1)^{3 or 4} with p=151 → (p−1)=150.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_151

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 151) := ⟨by decide⟩

theorem Kp_oneHundredFiftyOne_of_dvd {h : ℤ} (hh : (151 : ℤ) ∣ h) :
    Kp 151 h = (3375001 / 3375000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredFiftyOne_of_not_dvd {h : ℤ} (hh : ¬(151 : ℤ) ∣ h) :
    Kp 151 h = (506249999 / 506250000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredFiftyOne (h : ℤ) :
    Kp 151 h = if (151 : ℤ) ∣ h then (3375001 / 3375000 : ℚ) else (506249999 / 506250000 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredFiftyOne_of_dvd hh
  · exact Kp_oneHundredFiftyOne_of_not_dvd hh

def K2_151 (h : ℤ) : ℚ := Kp 2 h * Kp 151 h

theorem K2_151_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_151 h = 0 := by
  simp [K2_151, Kp_two_of_not_dvd h2]

theorem K2_151_of_two_and_oneHundredFiftyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (151 : ℤ) ∣ h) :
    K2_151 h = (2 : ℚ) * (3375001 / 3375000) := by
  simp [K2_151, Kp_two_of_dvd h2, Kp_oneHundredFiftyOne_of_dvd hp]

theorem K2_151_eq (h : ℤ) :
    K2_151 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (151 : ℤ) ∣ h then (3375001 / 3375000 : ℚ) else (506249999 / 506250000 : ℚ)) := by
  simp [K2_151, Kp_two h, Kp_oneHundredFiftyOne h]

end Brockian.Goldbach.WheelK2_151
