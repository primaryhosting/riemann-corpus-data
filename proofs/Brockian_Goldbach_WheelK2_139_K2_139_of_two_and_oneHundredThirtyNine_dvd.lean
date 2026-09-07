/-
  Brockian/GoldbachWheelK2_139.lean — exact local product K₂·K_139.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_139 from def: 1 ± 1/(p−1)^{3 or 4} with p=139 → (p−1)=138.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_139

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 139) := ⟨by decide⟩

theorem Kp_oneHundredThirtyNine_of_dvd {h : ℤ} (hh : (139 : ℤ) ∣ h) :
    Kp 139 h = (2628073 / 2628072 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirtyNine_of_not_dvd {h : ℤ} (hh : ¬(139 : ℤ) ∣ h) :
    Kp 139 h = (362673935 / 362673936 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirtyNine (h : ℤ) :
    Kp 139 h = if (139 : ℤ) ∣ h then (2628073 / 2628072 : ℚ) else (362673935 / 362673936 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredThirtyNine_of_dvd hh
  · exact Kp_oneHundredThirtyNine_of_not_dvd hh

def K2_139 (h : ℤ) : ℚ := Kp 2 h * Kp 139 h

theorem K2_139_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_139 h = 0 := by
  simp [K2_139, Kp_two_of_not_dvd h2]

theorem K2_139_of_two_and_oneHundredThirtyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (139 : ℤ) ∣ h) :
    K2_139 h = (2 : ℚ) * (2628073 / 2628072) := by
  simp [K2_139, Kp_two_of_dvd h2, Kp_oneHundredThirtyNine_of_dvd hp]

theorem K2_139_eq (h : ℤ) :
    K2_139 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (139 : ℤ) ∣ h then (2628073 / 2628072 : ℚ) else (362673935 / 362673936 : ℚ)) := by
  simp [K2_139, Kp_two h, Kp_oneHundredThirtyNine h]

end Brockian.Goldbach.WheelK2_139
