/-
  Brockian/GoldbachWheelK2_17.lean — exact local product K₂·K₁₇.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K₁₇ closed forms from def Kp: 1 ± 1/(p−1)^{3 or 4}.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_17

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- If `17 ∣ h`, K₁₇ = 1 + 1/16³ = 4097/4096. -/
theorem Kp_seventeen_of_dvd {h : ℤ} (hh : (17 : ℤ) ∣ h) :
    Kp 17 h = (4097 / 4096 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `17 ∤ h`, K₁₇ = 1 − 1/16⁴ = 65535/65536. -/
theorem Kp_seventeen_of_not_dvd {h : ℤ} (hh : ¬(17 : ℤ) ∣ h) :
    Kp 17 h = (65535 / 65536 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_seventeen (h : ℤ) :
    Kp 17 h = if (17 : ℤ) ∣ h then (4097 / 4096 : ℚ) else (65535 / 65536 : ℚ) := by
  split_ifs with hh
  · exact Kp_seventeen_of_dvd hh
  · exact Kp_seventeen_of_not_dvd hh

def K2_17 (h : ℤ) : ℚ := Kp 2 h * Kp 17 h

theorem K2_17_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_17 h = 0 := by
  simp [K2_17, Kp_two_of_not_dvd h2]

theorem K2_17_of_two_and_seventeen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h17 : (17 : ℤ) ∣ h) :
    K2_17 h = (2 : ℚ) * (4097 / 4096) := by
  simp [K2_17, Kp_two_of_dvd h2, Kp_seventeen_of_dvd h17]

theorem K2_17_eq (h : ℤ) :
    K2_17 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (17 : ℤ) ∣ h then (4097 / 4096 : ℚ) else (65535 / 65536 : ℚ)) := by
  simp [K2_17, Kp_two h, Kp_seventeen h]

end Brockian.Goldbach.WheelK2_17
