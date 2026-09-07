/-
  Brockian/GoldbachWheelK2_79.lean — exact local product K₂·K_79.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_79 from def: 1 ± 1/(p−1)^{3 or 4} with p=79 → (p−1)=78.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_79

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 79) := ⟨by decide⟩

theorem Kp_seventyNine_of_dvd {h : ℤ} (hh : (79 : ℤ) ∣ h) :
    Kp 79 h = (474553 / 474552 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_seventyNine_of_not_dvd {h : ℤ} (hh : ¬(79 : ℤ) ∣ h) :
    Kp 79 h = (37015055 / 37015056 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_seventyNine (h : ℤ) :
    Kp 79 h = if (79 : ℤ) ∣ h then (474553 / 474552 : ℚ) else (37015055 / 37015056 : ℚ) := by
  split_ifs with hh
  · exact Kp_seventyNine_of_dvd hh
  · exact Kp_seventyNine_of_not_dvd hh

def K2_79 (h : ℤ) : ℚ := Kp 2 h * Kp 79 h

theorem K2_79_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_79 h = 0 := by
  simp [K2_79, Kp_two_of_not_dvd h2]

theorem K2_79_of_two_and_seventyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (79 : ℤ) ∣ h) :
    K2_79 h = (2 : ℚ) * (474553 / 474552) := by
  simp [K2_79, Kp_two_of_dvd h2, Kp_seventyNine_of_dvd hp]

theorem K2_79_eq (h : ℤ) :
    K2_79 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (79 : ℤ) ∣ h then (474553 / 474552 : ℚ) else (37015055 / 37015056 : ℚ)) := by
  simp [K2_79, Kp_two h, Kp_seventyNine h]

end Brockian.Goldbach.WheelK2_79
