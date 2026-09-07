/-
  Brockian/GoldbachWheelK2_89.lean — exact local product K₂·K_89.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_89 from def: 1 ± 1/(p−1)^{3 or 4} with p=89 → (p−1)=88.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_89

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 89) := ⟨by decide⟩

theorem Kp_eightyNine_of_dvd {h : ℤ} (hh : (89 : ℤ) ∣ h) :
    Kp 89 h = (681473 / 681472 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_eightyNine_of_not_dvd {h : ℤ} (hh : ¬(89 : ℤ) ∣ h) :
    Kp 89 h = (59969535 / 59969536 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_eightyNine (h : ℤ) :
    Kp 89 h = if (89 : ℤ) ∣ h then (681473 / 681472 : ℚ) else (59969535 / 59969536 : ℚ) := by
  split_ifs with hh
  · exact Kp_eightyNine_of_dvd hh
  · exact Kp_eightyNine_of_not_dvd hh

def K2_89 (h : ℤ) : ℚ := Kp 2 h * Kp 89 h

theorem K2_89_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_89 h = 0 := by
  simp [K2_89, Kp_two_of_not_dvd h2]

theorem K2_89_of_two_and_eightyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (89 : ℤ) ∣ h) :
    K2_89 h = (2 : ℚ) * (681473 / 681472) := by
  simp [K2_89, Kp_two_of_dvd h2, Kp_eightyNine_of_dvd hp]

theorem K2_89_eq (h : ℤ) :
    K2_89 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (89 : ℤ) ∣ h then (681473 / 681472 : ℚ) else (59969535 / 59969536 : ℚ)) := by
  simp [K2_89, Kp_two h, Kp_eightyNine h]

end Brockian.Goldbach.WheelK2_89
