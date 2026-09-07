/-
  Brockian/GoldbachWheelK2_431.lean — exact local product K₂·K_431.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_431 from def: 1 ± 1/(p−1)^{3 or 4} with p=431 → (p−1)=430.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_431

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 431) := ⟨by decide⟩

theorem Kp_fourHundredThirtyOne_of_dvd {h : ℤ} (hh : (431 : ℤ) ∣ h) :
    Kp 431 h = (79507001 / 79507000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredThirtyOne_of_not_dvd {h : ℤ} (hh : ¬(431 : ℤ) ∣ h) :
    Kp 431 h = (34188009999 / 34188010000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredThirtyOne (h : ℤ) :
    Kp 431 h = if (431 : ℤ) ∣ h then (79507001 / 79507000 : ℚ) else (34188009999 / 34188010000 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredThirtyOne_of_dvd hh
  · exact Kp_fourHundredThirtyOne_of_not_dvd hh

def K2_431 (h : ℤ) : ℚ := Kp 2 h * Kp 431 h

theorem K2_431_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_431 h = 0 := by
  simp [K2_431, Kp_two_of_not_dvd h2]

theorem K2_431_of_two_and_fourHundredThirtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (431 : ℤ) ∣ h) :
    K2_431 h = (2 : ℚ) * (79507001 / 79507000) := by
  simp [K2_431, Kp_two_of_dvd h2, Kp_fourHundredThirtyOne_of_dvd hp]

theorem K2_431_eq (h : ℤ) :
    K2_431 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (431 : ℤ) ∣ h then (79507001 / 79507000 : ℚ) else (34188009999 / 34188010000 : ℚ)) := by
  simp [K2_431, Kp_two h, Kp_fourHundredThirtyOne h]

end Brockian.Goldbach.WheelK2_431
