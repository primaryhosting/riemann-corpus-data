/-
  Brockian/GoldbachWheelK2_73.lean — exact local product K₂·K_73.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_73 from def: 1 ± 1/(p−1)^{3 or 4} with p=73 → (p−1)=72.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_73

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 73) := ⟨by decide⟩

theorem Kp_seventyThree_of_dvd {h : ℤ} (hh : (73 : ℤ) ∣ h) :
    Kp 73 h = (373249 / 373248 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_seventyThree_of_not_dvd {h : ℤ} (hh : ¬(73 : ℤ) ∣ h) :
    Kp 73 h = (26873855 / 26873856 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_seventyThree (h : ℤ) :
    Kp 73 h = if (73 : ℤ) ∣ h then (373249 / 373248 : ℚ) else (26873855 / 26873856 : ℚ) := by
  split_ifs with hh
  · exact Kp_seventyThree_of_dvd hh
  · exact Kp_seventyThree_of_not_dvd hh

def K2_73 (h : ℤ) : ℚ := Kp 2 h * Kp 73 h

theorem K2_73_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_73 h = 0 := by
  simp [K2_73, Kp_two_of_not_dvd h2]

theorem K2_73_of_two_and_seventyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (73 : ℤ) ∣ h) :
    K2_73 h = (2 : ℚ) * (373249 / 373248) := by
  simp [K2_73, Kp_two_of_dvd h2, Kp_seventyThree_of_dvd hp]

theorem K2_73_eq (h : ℤ) :
    K2_73 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (73 : ℤ) ∣ h then (373249 / 373248 : ℚ) else (26873855 / 26873856 : ℚ)) := by
  simp [K2_73, Kp_two h, Kp_seventyThree h]

end Brockian.Goldbach.WheelK2_73
