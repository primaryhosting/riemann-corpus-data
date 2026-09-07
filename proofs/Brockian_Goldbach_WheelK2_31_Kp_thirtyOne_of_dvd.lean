/-
  Brockian/GoldbachWheelK2_31.lean — exact local product K₂·K_31.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_31 from def: 1 ± 1/(p−1)^{3 or 4} with p=31 → (p−1)=30.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_31

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 31) := ⟨by decide⟩

/-- If `31 ∣ h`, K_31 = 1 + 1/30³ = 27001/27000. -/
theorem Kp_thirtyOne_of_dvd {h : ℤ} (hh : (31 : ℤ) ∣ h) :
    Kp 31 h = (27001 / 27000 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `31 ∤ h`, K_31 = 1 − 1/30⁴ = 809999/810000. -/
theorem Kp_thirtyOne_of_not_dvd {h : ℤ} (hh : ¬(31 : ℤ) ∣ h) :
    Kp 31 h = (809999 / 810000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_thirtyOne (h : ℤ) :
    Kp 31 h = if (31 : ℤ) ∣ h then (27001 / 27000 : ℚ) else (809999 / 810000 : ℚ) := by
  split_ifs with hh
  · exact Kp_thirtyOne_of_dvd hh
  · exact Kp_thirtyOne_of_not_dvd hh

def K2_31 (h : ℤ) : ℚ := Kp 2 h * Kp 31 h

theorem K2_31_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_31 h = 0 := by
  simp [K2_31, Kp_two_of_not_dvd h2]

theorem K2_31_of_two_and_thirtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (31 : ℤ) ∣ h) :
    K2_31 h = (2 : ℚ) * (27001 / 27000) := by
  simp [K2_31, Kp_two_of_dvd h2, Kp_thirtyOne_of_dvd hp]

theorem K2_31_eq (h : ℤ) :
    K2_31 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (31 : ℤ) ∣ h then (27001 / 27000 : ℚ) else (809999 / 810000 : ℚ)) := by
  simp [K2_31, Kp_two h, Kp_thirtyOne h]

end Brockian.Goldbach.WheelK2_31
