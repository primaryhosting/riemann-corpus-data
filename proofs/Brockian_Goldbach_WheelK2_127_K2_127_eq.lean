/-
  Brockian/GoldbachWheelK2_127.lean — exact local product K₂·K_127.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_127 from def: 1 ± 1/(p−1)^{3 or 4} with p=127 → (p−1)=126.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_127

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 127) := ⟨by decide⟩

theorem Kp_oneHundredTwentySeven_of_dvd {h : ℤ} (hh : (127 : ℤ) ∣ h) :
    Kp 127 h = (2000377 / 2000376 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredTwentySeven_of_not_dvd {h : ℤ} (hh : ¬(127 : ℤ) ∣ h) :
    Kp 127 h = (252047375 / 252047376 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredTwentySeven (h : ℤ) :
    Kp 127 h = if (127 : ℤ) ∣ h then (2000377 / 2000376 : ℚ) else (252047375 / 252047376 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredTwentySeven_of_dvd hh
  · exact Kp_oneHundredTwentySeven_of_not_dvd hh

def K2_127 (h : ℤ) : ℚ := Kp 2 h * Kp 127 h

theorem K2_127_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_127 h = 0 := by
  simp [K2_127, Kp_two_of_not_dvd h2]

theorem K2_127_of_two_and_oneHundredTwentySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (127 : ℤ) ∣ h) :
    K2_127 h = (2 : ℚ) * (2000377 / 2000376) := by
  simp [K2_127, Kp_two_of_dvd h2, Kp_oneHundredTwentySeven_of_dvd hp]

theorem K2_127_eq (h : ℤ) :
    K2_127 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (127 : ℤ) ∣ h then (2000377 / 2000376 : ℚ) else (252047375 / 252047376 : ℚ)) := by
  simp [K2_127, Kp_two h, Kp_oneHundredTwentySeven h]

end Brockian.Goldbach.WheelK2_127
