/-
  Brockian/GoldbachWheelK2_149.lean — exact local product K₂·K_149.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_149 from def: 1 ± 1/(p−1)^{3 or 4} with p=149 → (p−1)=148.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_149

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 149) := ⟨by decide⟩

theorem Kp_oneHundredFortyNine_of_dvd {h : ℤ} (hh : (149 : ℤ) ∣ h) :
    Kp 149 h = (3241793 / 3241792 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredFortyNine_of_not_dvd {h : ℤ} (hh : ¬(149 : ℤ) ∣ h) :
    Kp 149 h = (479785215 / 479785216 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredFortyNine (h : ℤ) :
    Kp 149 h = if (149 : ℤ) ∣ h then (3241793 / 3241792 : ℚ) else (479785215 / 479785216 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredFortyNine_of_dvd hh
  · exact Kp_oneHundredFortyNine_of_not_dvd hh

def K2_149 (h : ℤ) : ℚ := Kp 2 h * Kp 149 h

theorem K2_149_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_149 h = 0 := by
  simp [K2_149, Kp_two_of_not_dvd h2]

theorem K2_149_of_two_and_oneHundredFortyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (149 : ℤ) ∣ h) :
    K2_149 h = (2 : ℚ) * (3241793 / 3241792) := by
  simp [K2_149, Kp_two_of_dvd h2, Kp_oneHundredFortyNine_of_dvd hp]

theorem K2_149_eq (h : ℤ) :
    K2_149 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (149 : ℤ) ∣ h then (3241793 / 3241792 : ℚ) else (479785215 / 479785216 : ℚ)) := by
  simp [K2_149, Kp_two h, Kp_oneHundredFortyNine h]

end Brockian.Goldbach.WheelK2_149
