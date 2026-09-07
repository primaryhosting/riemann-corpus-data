/-
  Brockian/GoldbachWheelK2_107.lean — exact local product K₂·K_107.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_107 from def: 1 ± 1/(p−1)^{3 or 4} with p=107 → (p−1)=106.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_107

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 107) := ⟨by decide⟩

theorem Kp_oneHundredSeven_of_dvd {h : ℤ} (hh : (107 : ℤ) ∣ h) :
    Kp 107 h = (1191017 / 1191016 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSeven_of_not_dvd {h : ℤ} (hh : ¬(107 : ℤ) ∣ h) :
    Kp 107 h = (126247695 / 126247696 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredSeven (h : ℤ) :
    Kp 107 h = if (107 : ℤ) ∣ h then (1191017 / 1191016 : ℚ) else (126247695 / 126247696 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredSeven_of_dvd hh
  · exact Kp_oneHundredSeven_of_not_dvd hh

def K2_107 (h : ℤ) : ℚ := Kp 2 h * Kp 107 h

theorem K2_107_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_107 h = 0 := by
  simp [K2_107, Kp_two_of_not_dvd h2]

theorem K2_107_of_two_and_oneHundredSeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (107 : ℤ) ∣ h) :
    K2_107 h = (2 : ℚ) * (1191017 / 1191016) := by
  simp [K2_107, Kp_two_of_dvd h2, Kp_oneHundredSeven_of_dvd hp]

theorem K2_107_eq (h : ℤ) :
    K2_107 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (107 : ℤ) ∣ h then (1191017 / 1191016 : ℚ) else (126247695 / 126247696 : ℚ)) := by
  simp [K2_107, Kp_two h, Kp_oneHundredSeven h]

end Brockian.Goldbach.WheelK2_107
