/-
  Brockian/GoldbachWheelK2_61.lean — exact local product K₂·K_61.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_61 from def: 1 ± 1/(p−1)^{3 or 4} with p=61 → (p−1)=60.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_61

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 61) := ⟨by decide⟩

theorem Kp_sixtyOne_of_dvd {h : ℤ} (hh : (61 : ℤ) ∣ h) :
    Kp 61 h = (216001 / 216000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixtyOne_of_not_dvd {h : ℤ} (hh : ¬(61 : ℤ) ∣ h) :
    Kp 61 h = (12959999 / 12960000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixtyOne (h : ℤ) :
    Kp 61 h = if (61 : ℤ) ∣ h then (216001 / 216000 : ℚ) else (12959999 / 12960000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixtyOne_of_dvd hh
  · exact Kp_sixtyOne_of_not_dvd hh

def K2_61 (h : ℤ) : ℚ := Kp 2 h * Kp 61 h

theorem K2_61_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_61 h = 0 := by
  simp [K2_61, Kp_two_of_not_dvd h2]

theorem K2_61_of_two_and_sixtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (61 : ℤ) ∣ h) :
    K2_61 h = (2 : ℚ) * (216001 / 216000) := by
  simp [K2_61, Kp_two_of_dvd h2, Kp_sixtyOne_of_dvd hp]

theorem K2_61_eq (h : ℤ) :
    K2_61 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (61 : ℤ) ∣ h then (216001 / 216000 : ℚ) else (12959999 / 12960000 : ℚ)) := by
  simp [K2_61, Kp_two h, Kp_sixtyOne h]

end Brockian.Goldbach.WheelK2_61
