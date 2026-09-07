/-
  Brockian/GoldbachWheelK2_157.lean — exact local product K₂·K_157.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_157 from def: 1 ± 1/(p−1)^{3 or 4} with p=157 → (p−1)=156.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_157

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 157) := ⟨by decide⟩

theorem Kp_oneHundredFiftySeven_of_dvd {h : ℤ} (hh : (157 : ℤ) ∣ h) :
    Kp 157 h = (3796417 / 3796416 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredFiftySeven_of_not_dvd {h : ℤ} (hh : ¬(157 : ℤ) ∣ h) :
    Kp 157 h = (592240895 / 592240896 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredFiftySeven (h : ℤ) :
    Kp 157 h = if (157 : ℤ) ∣ h then (3796417 / 3796416 : ℚ) else (592240895 / 592240896 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredFiftySeven_of_dvd hh
  · exact Kp_oneHundredFiftySeven_of_not_dvd hh

def K2_157 (h : ℤ) : ℚ := Kp 2 h * Kp 157 h

theorem K2_157_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_157 h = 0 := by
  simp [K2_157, Kp_two_of_not_dvd h2]

theorem K2_157_of_two_and_oneHundredFiftySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (157 : ℤ) ∣ h) :
    K2_157 h = (2 : ℚ) * (3796417 / 3796416) := by
  simp [K2_157, Kp_two_of_dvd h2, Kp_oneHundredFiftySeven_of_dvd hp]

theorem K2_157_eq (h : ℤ) :
    K2_157 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (157 : ℤ) ∣ h then (3796417 / 3796416 : ℚ) else (592240895 / 592240896 : ℚ)) := by
  simp [K2_157, Kp_two h, Kp_oneHundredFiftySeven h]

end Brockian.Goldbach.WheelK2_157
