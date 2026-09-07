/-
  Brockian/GoldbachWheelK2_41.lean — exact local product K₂·K_41.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_41 from def: 1 ± 1/(p−1)^{3 or 4} with p=41 → (p−1)=40.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_41

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- If `41 ∣ h`, K_41 = 1 + 1/40³ = 64001/64000. -/
theorem Kp_fortyOne_of_dvd {h : ℤ} (hh : (41 : ℤ) ∣ h) :
    Kp 41 h = (64001 / 64000 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `41 ∤ h`, K_41 = 1 − 1/40⁴ = 2559999/2560000. -/
theorem Kp_fortyOne_of_not_dvd {h : ℤ} (hh : ¬(41 : ℤ) ∣ h) :
    Kp 41 h = (2559999 / 2560000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fortyOne (h : ℤ) :
    Kp 41 h = if (41 : ℤ) ∣ h then (64001 / 64000 : ℚ) else (2559999 / 2560000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fortyOne_of_dvd hh
  · exact Kp_fortyOne_of_not_dvd hh

def K2_41 (h : ℤ) : ℚ := Kp 2 h * Kp 41 h

theorem K2_41_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_41 h = 0 := by
  simp [K2_41, Kp_two_of_not_dvd h2]

theorem K2_41_of_two_and_fortyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (41 : ℤ) ∣ h) :
    K2_41 h = (2 : ℚ) * (64001 / 64000) := by
  simp [K2_41, Kp_two_of_dvd h2, Kp_fortyOne_of_dvd hp]

theorem K2_41_eq (h : ℤ) :
    K2_41 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (41 : ℤ) ∣ h then (64001 / 64000 : ℚ) else (2559999 / 2560000 : ℚ)) := by
  simp [K2_41, Kp_two h, Kp_fortyOne h]

end Brockian.Goldbach.WheelK2_41
