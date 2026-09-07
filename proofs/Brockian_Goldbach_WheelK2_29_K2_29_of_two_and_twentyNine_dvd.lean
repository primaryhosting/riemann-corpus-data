/-
  Brockian/GoldbachWheelK2_29.lean — exact local product K₂·K₂₉.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K₂₉ from def: 1 ± 1/(p−1)^{3 or 4} with p=29 → (p−1)=28.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_29

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- If `29 ∣ h`, K₂₉ = 1 + 1/28³ = 21953/21952. -/
theorem Kp_twentyNine_of_dvd {h : ℤ} (hh : (29 : ℤ) ∣ h) :
    Kp 29 h = (21953 / 21952 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `29 ∤ h`, K₂₉ = 1 − 1/28⁴ = 614655/614656. -/
theorem Kp_twentyNine_of_not_dvd {h : ℤ} (hh : ¬(29 : ℤ) ∣ h) :
    Kp 29 h = (614655 / 614656 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twentyNine (h : ℤ) :
    Kp 29 h = if (29 : ℤ) ∣ h then (21953 / 21952 : ℚ) else (614655 / 614656 : ℚ) := by
  split_ifs with hh
  · exact Kp_twentyNine_of_dvd hh
  · exact Kp_twentyNine_of_not_dvd hh

def K2_29 (h : ℤ) : ℚ := Kp 2 h * Kp 29 h

theorem K2_29_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_29 h = 0 := by
  simp [K2_29, Kp_two_of_not_dvd h2]

theorem K2_29_of_two_and_twentyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h29 : (29 : ℤ) ∣ h) :
    K2_29 h = (2 : ℚ) * (21953 / 21952) := by
  simp [K2_29, Kp_two_of_dvd h2, Kp_twentyNine_of_dvd h29]

theorem K2_29_eq (h : ℤ) :
    K2_29 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (29 : ℤ) ∣ h then (21953 / 21952 : ℚ) else (614655 / 614656 : ℚ)) := by
  simp [K2_29, Kp_two h, Kp_twentyNine h]

end Brockian.Goldbach.WheelK2_29
