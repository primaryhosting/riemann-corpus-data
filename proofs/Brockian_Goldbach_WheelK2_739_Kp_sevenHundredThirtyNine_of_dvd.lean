/-
  Brockian/GoldbachWheelK2_739.lean — exact local product K₂·K_739.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_739 from def: 1 ± 1/(p−1)^{3 or 4} with p=739 → (p−1)=738.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_739

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 739) := ⟨by decide⟩

theorem Kp_sevenHundredThirtyNine_of_dvd {h : ℤ} (hh : (739 : ℤ) ∣ h) :
    Kp 739 h = (401947273 / 401947272 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredThirtyNine_of_not_dvd {h : ℤ} (hh : ¬(739 : ℤ) ∣ h) :
    Kp 739 h = (296637086735 / 296637086736 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredThirtyNine (h : ℤ) :
    Kp 739 h = if (739 : ℤ) ∣ h then (401947273 / 401947272 : ℚ) else (296637086735 / 296637086736 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredThirtyNine_of_dvd hh
  · exact Kp_sevenHundredThirtyNine_of_not_dvd hh

def K2_739 (h : ℤ) : ℚ := Kp 2 h * Kp 739 h

theorem K2_739_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_739 h = 0 := by
  simp [K2_739, Kp_two_of_not_dvd h2]

theorem K2_739_of_two_and_sevenHundredThirtyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (739 : ℤ) ∣ h) :
    K2_739 h = (2 : ℚ) * (401947273 / 401947272) := by
  simp [K2_739, Kp_two_of_dvd h2, Kp_sevenHundredThirtyNine_of_dvd hp]

theorem K2_739_eq (h : ℤ) :
    K2_739 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (739 : ℤ) ∣ h then (401947273 / 401947272 : ℚ) else (296637086735 / 296637086736 : ℚ)) := by
  simp [K2_739, Kp_two h, Kp_sevenHundredThirtyNine h]

end Brockian.Goldbach.WheelK2_739
