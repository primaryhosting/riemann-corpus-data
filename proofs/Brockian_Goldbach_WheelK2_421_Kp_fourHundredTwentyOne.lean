/-
  Brockian/GoldbachWheelK2_421.lean — exact local product K₂·K_421.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_421 from def: 1 ± 1/(p−1)^{3 or 4} with p=421 → (p−1)=420.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_421

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 421) := ⟨by decide⟩

theorem Kp_fourHundredTwentyOne_of_dvd {h : ℤ} (hh : (421 : ℤ) ∣ h) :
    Kp 421 h = (74088001 / 74088000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredTwentyOne_of_not_dvd {h : ℤ} (hh : ¬(421 : ℤ) ∣ h) :
    Kp 421 h = (31116959999 / 31116960000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredTwentyOne (h : ℤ) :
    Kp 421 h = if (421 : ℤ) ∣ h then (74088001 / 74088000 : ℚ) else (31116959999 / 31116960000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredTwentyOne_of_dvd hh
  · exact Kp_fourHundredTwentyOne_of_not_dvd hh

def K2_421 (h : ℤ) : ℚ := Kp 2 h * Kp 421 h

theorem K2_421_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_421 h = 0 := by
  simp [K2_421, Kp_two_of_not_dvd h2]

theorem K2_421_of_two_and_fourHundredTwentyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (421 : ℤ) ∣ h) :
    K2_421 h = (2 : ℚ) * (74088001 / 74088000) := by
  simp [K2_421, Kp_two_of_dvd h2, Kp_fourHundredTwentyOne_of_dvd hp]

theorem K2_421_eq (h : ℤ) :
    K2_421 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (421 : ℤ) ∣ h then (74088001 / 74088000 : ℚ) else (31116959999 / 31116960000 : ℚ)) := by
  simp [K2_421, Kp_two h, Kp_fourHundredTwentyOne h]

end Brockian.Goldbach.WheelK2_421
