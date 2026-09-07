/-
  Brockian/GoldbachWheelK2_443.lean — exact local product K₂·K_443.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_443 from def: 1 ± 1/(p−1)^{3 or 4} with p=443 → (p−1)=442.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_443

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 443) := ⟨by decide⟩

theorem Kp_fourHundredFortyThree_of_dvd {h : ℤ} (hh : (443 : ℤ) ∣ h) :
    Kp 443 h = (86350889 / 86350888 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredFortyThree_of_not_dvd {h : ℤ} (hh : ¬(443 : ℤ) ∣ h) :
    Kp 443 h = (38167092495 / 38167092496 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredFortyThree (h : ℤ) :
    Kp 443 h = if (443 : ℤ) ∣ h then (86350889 / 86350888 : ℚ) else (38167092495 / 38167092496 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredFortyThree_of_dvd hh
  · exact Kp_fourHundredFortyThree_of_not_dvd hh

def K2_443 (h : ℤ) : ℚ := Kp 2 h * Kp 443 h

theorem K2_443_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_443 h = 0 := by
  simp [K2_443, Kp_two_of_not_dvd h2]

theorem K2_443_of_two_and_fourHundredFortyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (443 : ℤ) ∣ h) :
    K2_443 h = (2 : ℚ) * (86350889 / 86350888) := by
  simp [K2_443, Kp_two_of_dvd h2, Kp_fourHundredFortyThree_of_dvd hp]

theorem K2_443_eq (h : ℤ) :
    K2_443 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (443 : ℤ) ∣ h then (86350889 / 86350888 : ℚ) else (38167092495 / 38167092496 : ℚ)) := by
  simp [K2_443, Kp_two h, Kp_fourHundredFortyThree h]

end Brockian.Goldbach.WheelK2_443
