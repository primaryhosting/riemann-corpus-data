/-
  Brockian/GoldbachWheelK2_409.lean — exact local product K₂·K_409.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_409 from def: 1 ± 1/(p−1)^{3 or 4} with p=409 → (p−1)=408.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_409

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 409) := ⟨by decide⟩

theorem Kp_fourHundredNine_of_dvd {h : ℤ} (hh : (409 : ℤ) ∣ h) :
    Kp 409 h = (67917313 / 67917312 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNine_of_not_dvd {h : ℤ} (hh : ¬(409 : ℤ) ∣ h) :
    Kp 409 h = (27710263295 / 27710263296 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNine (h : ℤ) :
    Kp 409 h = if (409 : ℤ) ∣ h then (67917313 / 67917312 : ℚ) else (27710263295 / 27710263296 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredNine_of_dvd hh
  · exact Kp_fourHundredNine_of_not_dvd hh

def K2_409 (h : ℤ) : ℚ := Kp 2 h * Kp 409 h

theorem K2_409_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_409 h = 0 := by
  simp [K2_409, Kp_two_of_not_dvd h2]

theorem K2_409_of_two_and_fourHundredNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (409 : ℤ) ∣ h) :
    K2_409 h = (2 : ℚ) * (67917313 / 67917312) := by
  simp [K2_409, Kp_two_of_dvd h2, Kp_fourHundredNine_of_dvd hp]

theorem K2_409_eq (h : ℤ) :
    K2_409 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (409 : ℤ) ∣ h then (67917313 / 67917312 : ℚ) else (27710263295 / 27710263296 : ℚ)) := by
  simp [K2_409, Kp_two h, Kp_fourHundredNine h]

end Brockian.Goldbach.WheelK2_409
