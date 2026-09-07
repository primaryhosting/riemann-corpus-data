/-
  Brockian/GoldbachWheelK2_131.lean — exact local product K₂·K_131.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_131 from def: 1 ± 1/(p−1)^{3 or 4} with p=131 → (p−1)=130.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_131

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 131) := ⟨by decide⟩

theorem Kp_oneHundredThirtyOne_of_dvd {h : ℤ} (hh : (131 : ℤ) ∣ h) :
    Kp 131 h = (2197001 / 2197000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirtyOne_of_not_dvd {h : ℤ} (hh : ¬(131 : ℤ) ∣ h) :
    Kp 131 h = (285609999 / 285610000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThirtyOne (h : ℤ) :
    Kp 131 h = if (131 : ℤ) ∣ h then (2197001 / 2197000 : ℚ) else (285609999 / 285610000 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredThirtyOne_of_dvd hh
  · exact Kp_oneHundredThirtyOne_of_not_dvd hh

def K2_131 (h : ℤ) : ℚ := Kp 2 h * Kp 131 h

theorem K2_131_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_131 h = 0 := by
  simp [K2_131, Kp_two_of_not_dvd h2]

theorem K2_131_of_two_and_oneHundredThirtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (131 : ℤ) ∣ h) :
    K2_131 h = (2 : ℚ) * (2197001 / 2197000) := by
  simp [K2_131, Kp_two_of_dvd h2, Kp_oneHundredThirtyOne_of_dvd hp]

theorem K2_131_eq (h : ℤ) :
    K2_131 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (131 : ℤ) ∣ h then (2197001 / 2197000 : ℚ) else (285609999 / 285610000 : ℚ)) := by
  simp [K2_131, Kp_two h, Kp_oneHundredThirtyOne h]

end Brockian.Goldbach.WheelK2_131
