/-
  Brockian/GoldbachWheelK2_47.lean — exact local product K₂·K_47.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_47 from def: 1 ± 1/(p−1)^{3 or 4} with p=47 → (p−1)=46.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_47

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 47) := ⟨by decide⟩

theorem Kp_fortySeven_of_dvd {h : ℤ} (hh : (47 : ℤ) ∣ h) :
    Kp 47 h = (97337 / 97336 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fortySeven_of_not_dvd {h : ℤ} (hh : ¬(47 : ℤ) ∣ h) :
    Kp 47 h = (4477455 / 4477456 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fortySeven (h : ℤ) :
    Kp 47 h = if (47 : ℤ) ∣ h then (97337 / 97336 : ℚ) else (4477455 / 4477456 : ℚ) := by
  split_ifs with hh
  · exact Kp_fortySeven_of_dvd hh
  · exact Kp_fortySeven_of_not_dvd hh

def K2_47 (h : ℤ) : ℚ := Kp 2 h * Kp 47 h

theorem K2_47_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_47 h = 0 := by
  simp [K2_47, Kp_two_of_not_dvd h2]

theorem K2_47_of_two_and_fortySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (47 : ℤ) ∣ h) :
    K2_47 h = (2 : ℚ) * (97337 / 97336) := by
  simp [K2_47, Kp_two_of_dvd h2, Kp_fortySeven_of_dvd hp]

theorem K2_47_eq (h : ℤ) :
    K2_47 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (47 : ℤ) ∣ h then (97337 / 97336 : ℚ) else (4477455 / 4477456 : ℚ)) := by
  simp [K2_47, Kp_two h, Kp_fortySeven h]

end Brockian.Goldbach.WheelK2_47
