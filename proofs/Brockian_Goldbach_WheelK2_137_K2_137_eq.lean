/-
  Brockian/GoldbachWheelK2_137.lean — exact local product K₂·K_137.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_137 from def: 1 ± 1/(p−1)^{3 or 4} with p=137 → (p−1)=136.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_137

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 137) := ⟨by decide⟩

theorem Kp_oneHundredThirtySeven_of_dvd {h : ℤ} (hh : (137 : ℤ) ∣ h) :
    Kp 137 h = (2515457 / 2515456 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirtySeven_of_not_dvd {h : ℤ} (hh : ¬(137 : ℤ) ∣ h) :
    Kp 137 h = (342102015 / 342102016 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirtySeven (h : ℤ) :
    Kp 137 h = if (137 : ℤ) ∣ h then (2515457 / 2515456 : ℚ) else (342102015 / 342102016 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredThirtySeven_of_dvd hh
  · exact Kp_oneHundredThirtySeven_of_not_dvd hh

def K2_137 (h : ℤ) : ℚ := Kp 2 h * Kp 137 h

theorem K2_137_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_137 h = 0 := by
  simp [K2_137, Kp_two_of_not_dvd h2]

theorem K2_137_of_two_and_oneHundredThirtySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (137 : ℤ) ∣ h) :
    K2_137 h = (2 : ℚ) * (2515457 / 2515456) := by
  simp [K2_137, Kp_two_of_dvd h2, Kp_oneHundredThirtySeven_of_dvd hp]

theorem K2_137_eq (h : ℤ) :
    K2_137 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (137 : ℤ) ∣ h then (2515457 / 2515456 : ℚ) else (342102015 / 342102016 : ℚ)) := by
  simp [K2_137, Kp_two h, Kp_oneHundredThirtySeven h]

end Brockian.Goldbach.WheelK2_137
