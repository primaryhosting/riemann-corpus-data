/-
  Brockian/GoldbachWheelK2_97.lean — exact local product K₂·K_97.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_97 from def: 1 ± 1/(p−1)^{3 or 4} with p=97 → (p−1)=96.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_97

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 97) := ⟨by decide⟩

theorem Kp_ninetySeven_of_dvd {h : ℤ} (hh : (97 : ℤ) ∣ h) :
    Kp 97 h = (884737 / 884736 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_ninetySeven_of_not_dvd {h : ℤ} (hh : ¬(97 : ℤ) ∣ h) :
    Kp 97 h = (84934655 / 84934656 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_ninetySeven (h : ℤ) :
    Kp 97 h = if (97 : ℤ) ∣ h then (884737 / 884736 : ℚ) else (84934655 / 84934656 : ℚ) := by
  split_ifs with hh
  · exact Kp_ninetySeven_of_dvd hh
  · exact Kp_ninetySeven_of_not_dvd hh

def K2_97 (h : ℤ) : ℚ := Kp 2 h * Kp 97 h

theorem K2_97_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_97 h = 0 := by
  simp [K2_97, Kp_two_of_not_dvd h2]

theorem K2_97_of_two_and_ninetySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (97 : ℤ) ∣ h) :
    K2_97 h = (2 : ℚ) * (884737 / 884736) := by
  simp [K2_97, Kp_two_of_dvd h2, Kp_ninetySeven_of_dvd hp]

theorem K2_97_eq (h : ℤ) :
    K2_97 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (97 : ℤ) ∣ h then (884737 / 884736 : ℚ) else (84934655 / 84934656 : ℚ)) := by
  simp [K2_97, Kp_two h, Kp_ninetySeven h]

end Brockian.Goldbach.WheelK2_97
