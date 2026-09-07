/-
  Brockian/GoldbachWheelK2_109.lean — exact local product K₂·K_109.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_109 from def: 1 ± 1/(p−1)^{3 or 4} with p=109 → (p−1)=108.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_109

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 109) := ⟨by decide⟩

theorem Kp_oneHundredNine_of_dvd {h : ℤ} (hh : (109 : ℤ) ∣ h) :
    Kp 109 h = (1259713 / 1259712 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNine_of_not_dvd {h : ℤ} (hh : ¬(109 : ℤ) ∣ h) :
    Kp 109 h = (136048895 / 136048896 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNine (h : ℤ) :
    Kp 109 h = if (109 : ℤ) ∣ h then (1259713 / 1259712 : ℚ) else (136048895 / 136048896 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredNine_of_dvd hh
  · exact Kp_oneHundredNine_of_not_dvd hh

def K2_109 (h : ℤ) : ℚ := Kp 2 h * Kp 109 h

theorem K2_109_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_109 h = 0 := by
  simp [K2_109, Kp_two_of_not_dvd h2]

theorem K2_109_of_two_and_oneHundredNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (109 : ℤ) ∣ h) :
    K2_109 h = (2 : ℚ) * (1259713 / 1259712) := by
  simp [K2_109, Kp_two_of_dvd h2, Kp_oneHundredNine_of_dvd hp]

theorem K2_109_eq (h : ℤ) :
    K2_109 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (109 : ℤ) ∣ h then (1259713 / 1259712 : ℚ) else (136048895 / 136048896 : ℚ)) := by
  simp [K2_109, Kp_two h, Kp_oneHundredNine h]

end Brockian.Goldbach.WheelK2_109
