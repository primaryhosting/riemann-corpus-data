/-
  Brockian/GoldbachWheelK2_37.lean — exact local product K₂·K₃₇.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K₃₇ from def: 1 ± 1/(p−1)^{3 or 4} with p=37 → (p−1)=36.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_37

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- If `37 ∣ h`, K₃₇ = 1 + 1/36³ = 46657/46656. -/
theorem Kp_thirtySeven_of_dvd {h : ℤ} (hh : (37 : ℤ) ∣ h) :
    Kp 37 h = (46657 / 46656 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `37 ∤ h`, K₃₇ = 1 − 1/36⁴ = 1679615/1679616. -/
theorem Kp_thirtySeven_of_not_dvd {h : ℤ} (hh : ¬(37 : ℤ) ∣ h) :
    Kp 37 h = (1679615 / 1679616 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_thirtySeven (h : ℤ) :
    Kp 37 h = if (37 : ℤ) ∣ h then (46657 / 46656 : ℚ) else (1679615 / 1679616 : ℚ) := by
  split_ifs with hh
  · exact Kp_thirtySeven_of_dvd hh
  · exact Kp_thirtySeven_of_not_dvd hh

def K2_37 (h : ℤ) : ℚ := Kp 2 h * Kp 37 h

theorem K2_37_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_37 h = 0 := by
  simp [K2_37, Kp_two_of_not_dvd h2]

theorem K2_37_of_two_and_thirtySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h37 : (37 : ℤ) ∣ h) :
    K2_37 h = (2 : ℚ) * (46657 / 46656) := by
  simp [K2_37, Kp_two_of_dvd h2, Kp_thirtySeven_of_dvd h37]

theorem K2_37_eq (h : ℤ) :
    K2_37 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (37 : ℤ) ∣ h then (46657 / 46656 : ℚ) else (1679615 / 1679616 : ℚ)) := by
  simp [K2_37, Kp_two h, Kp_thirtySeven h]

end Brockian.Goldbach.WheelK2_37
