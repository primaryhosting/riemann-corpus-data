/-
  Brockian/GoldbachWheelK2_71.lean — exact local product K₂·K_71.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_71 from def: 1 ± 1/(p−1)^{3 or 4} with p=71 → (p−1)=70.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_71

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem Kp_seventyOne_of_dvd {h : ℤ} (hh : (71 : ℤ) ∣ h) :
    Kp 71 h = (343001 / 343000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_seventyOne_of_not_dvd {h : ℤ} (hh : ¬(71 : ℤ) ∣ h) :
    Kp 71 h = (24009999 / 24010000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_seventyOne (h : ℤ) :
    Kp 71 h = if (71 : ℤ) ∣ h then (343001 / 343000 : ℚ) else (24009999 / 24010000 : ℚ) := by
  split_ifs with hh
  · exact Kp_seventyOne_of_dvd hh
  · exact Kp_seventyOne_of_not_dvd hh

def K2_71 (h : ℤ) : ℚ := Kp 2 h * Kp 71 h

theorem K2_71_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_71 h = 0 := by
  simp [K2_71, Kp_two_of_not_dvd h2]

theorem K2_71_of_two_and_seventyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (71 : ℤ) ∣ h) :
    K2_71 h = (2 : ℚ) * (343001 / 343000) := by
  simp [K2_71, Kp_two_of_dvd h2, Kp_seventyOne_of_dvd hp]

theorem K2_71_eq (h : ℤ) :
    K2_71 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (71 : ℤ) ∣ h then (343001 / 343000 : ℚ) else (24009999 / 24010000 : ℚ)) := by
  simp [K2_71, Kp_two h, Kp_seventyOne h]

end Brockian.Goldbach.WheelK2_71
