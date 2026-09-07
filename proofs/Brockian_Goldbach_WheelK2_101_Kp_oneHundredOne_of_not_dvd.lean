/-
  Brockian/GoldbachWheelK2_101.lean — exact local product K₂·K_101.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_101 from def: 1 ± 1/(p−1)^{3 or 4} with p=101 → (p−1)=100.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_101

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem Kp_oneHundredOne_of_dvd {h : ℤ} (hh : (101 : ℤ) ∣ h) :
    Kp 101 h = (1000001 / 1000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredOne_of_not_dvd {h : ℤ} (hh : ¬(101 : ℤ) ∣ h) :
    Kp 101 h = (99999999 / 100000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredOne (h : ℤ) :
    Kp 101 h = if (101 : ℤ) ∣ h then (1000001 / 1000000 : ℚ) else (99999999 / 100000000 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredOne_of_dvd hh
  · exact Kp_oneHundredOne_of_not_dvd hh

def K2_101 (h : ℤ) : ℚ := Kp 2 h * Kp 101 h

theorem K2_101_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_101 h = 0 := by
  simp [K2_101, Kp_two_of_not_dvd h2]

theorem K2_101_of_two_and_oneHundredOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (101 : ℤ) ∣ h) :
    K2_101 h = (2 : ℚ) * (1000001 / 1000000) := by
  simp [K2_101, Kp_two_of_dvd h2, Kp_oneHundredOne_of_dvd hp]

theorem K2_101_eq (h : ℤ) :
    K2_101 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (101 : ℤ) ∣ h then (1000001 / 1000000 : ℚ) else (99999999 / 100000000 : ℚ)) := by
  simp [K2_101, Kp_two h, Kp_oneHundredOne h]

end Brockian.Goldbach.WheelK2_101
