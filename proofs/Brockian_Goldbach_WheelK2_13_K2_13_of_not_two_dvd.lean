/-
  Brockian/GoldbachWheelK2_13.lean — exact local product K₂·K₁₃.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity
import Brockian.GoldbachWheelExtended

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_13

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity
open Brockian.Goldbach.WheelExtended

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 13) := ⟨by decide⟩

def K2_13 (h : ℤ) : ℚ := Kp 2 h * Kp 13 h

theorem K2_13_of_not_two_dvd {h : ℤ} (h2 : ¬ (2 : ℤ) ∣ h) : K2_13 h = 0 := by
  simp [K2_13, Kp_two_of_not_dvd h2]

theorem K2_13_of_two_and_thirteen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h13 : (13 : ℤ) ∣ h) :
    K2_13 h = (2 : ℚ) * (1729 / 1728) := by
  simp [K2_13, Kp_two_of_dvd h2, Kp_thirteen_of_dvd h13]

theorem K2_13_eq (h : ℤ) :
    K2_13 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (13 : ℤ) ∣ h then (1729 / 1728 : ℚ) else (20735 / 20736 : ℚ)) := by
  simp [K2_13, Kp_two h, Kp_thirteen h]

end Brockian.Goldbach.WheelK2_13
