/-
  Brockian/GoldbachWheelK2_113.lean — exact local product K₂·K_113.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_113 from def: 1 ± 1/(p−1)^{3 or 4} with p=113 → (p−1)=112.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_113

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 113) := ⟨by decide⟩

theorem Kp_oneHundredThirteen_of_dvd {h : ℤ} (hh : (113 : ℤ) ∣ h) :
    Kp 113 h = (1404929 / 1404928 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirteen_of_not_dvd {h : ℤ} (hh : ¬(113 : ℤ) ∣ h) :
    Kp 113 h = (157351935 / 157351936 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirteen (h : ℤ) :
    Kp 113 h = if (113 : ℤ) ∣ h then (1404929 / 1404928 : ℚ) else (157351935 / 157351936 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredThirteen_of_dvd hh
  · exact Kp_oneHundredThirteen_of_not_dvd hh

def K2_113 (h : ℤ) : ℚ := Kp 2 h * Kp 113 h

theorem K2_113_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_113 h = 0 := by
  simp [K2_113, Kp_two_of_not_dvd h2]

theorem K2_113_of_two_and_oneHundredThirteen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (113 : ℤ) ∣ h) :
    K2_113 h = (2 : ℚ) * (1404929 / 1404928) := by
  simp [K2_113, Kp_two_of_dvd h2, Kp_oneHundredThirteen_of_dvd hp]

theorem K2_113_eq (h : ℤ) :
    K2_113 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (113 : ℤ) ∣ h then (1404929 / 1404928 : ℚ) else (157351935 / 157351936 : ℚ)) := by
  simp [K2_113, Kp_two h, Kp_oneHundredThirteen h]

end Brockian.Goldbach.WheelK2_113
