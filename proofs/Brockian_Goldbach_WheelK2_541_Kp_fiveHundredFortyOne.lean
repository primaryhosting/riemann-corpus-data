/-
  Brockian/GoldbachWheelK2_541.lean — exact local product K₂·K_541.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_541 from def: 1 ± 1/(p−1)^{3 or 4} with p=541 → (p−1)=540.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_541

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 541) := ⟨by decide⟩

theorem Kp_fiveHundredFortyOne_of_dvd {h : ℤ} (hh : (541 : ℤ) ∣ h) :
    Kp 541 h = (157464001 / 157464000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredFortyOne_of_not_dvd {h : ℤ} (hh : ¬(541 : ℤ) ∣ h) :
    Kp 541 h = (85030559999 / 85030560000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredFortyOne (h : ℤ) :
    Kp 541 h = if (541 : ℤ) ∣ h then (157464001 / 157464000 : ℚ) else (85030559999 / 85030560000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredFortyOne_of_dvd hh
  · exact Kp_fiveHundredFortyOne_of_not_dvd hh

def K2_541 (h : ℤ) : ℚ := Kp 2 h * Kp 541 h

theorem K2_541_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_541 h = 0 := by
  simp [K2_541, Kp_two_of_not_dvd h2]

theorem K2_541_of_two_and_fiveHundredFortyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (541 : ℤ) ∣ h) :
    K2_541 h = (2 : ℚ) * (157464001 / 157464000) := by
  simp [K2_541, Kp_two_of_dvd h2, Kp_fiveHundredFortyOne_of_dvd hp]

theorem K2_541_eq (h : ℤ) :
    K2_541 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (541 : ℤ) ∣ h then (157464001 / 157464000 : ℚ) else (85030559999 / 85030560000 : ℚ)) := by
  simp [K2_541, Kp_two h, Kp_fiveHundredFortyOne h]

end Brockian.Goldbach.WheelK2_541
