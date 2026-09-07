/-
  Brockian/GoldbachWheelK2_379.lean — exact local product K₂·K_379.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_379 from def: 1 ± 1/(p−1)^{3 or 4} with p=379 → (p−1)=378.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_379

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 379) := ⟨by decide⟩

theorem Kp_threeHundredSeventyNine_of_dvd {h : ℤ} (hh : (379 : ℤ) ∣ h) :
    Kp 379 h = (54010153 / 54010152 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeventyNine_of_not_dvd {h : ℤ} (hh : ¬(379 : ℤ) ∣ h) :
    Kp 379 h = (20415837455 / 20415837456 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeventyNine (h : ℤ) :
    Kp 379 h = if (379 : ℤ) ∣ h then (54010153 / 54010152 : ℚ) else (20415837455 / 20415837456 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredSeventyNine_of_dvd hh
  · exact Kp_threeHundredSeventyNine_of_not_dvd hh

def K2_379 (h : ℤ) : ℚ := Kp 2 h * Kp 379 h

theorem K2_379_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_379 h = 0 := by
  simp [K2_379, Kp_two_of_not_dvd h2]

theorem K2_379_of_two_and_threeHundredSeventyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (379 : ℤ) ∣ h) :
    K2_379 h = (2 : ℚ) * (54010153 / 54010152) := by
  simp [K2_379, Kp_two_of_dvd h2, Kp_threeHundredSeventyNine_of_dvd hp]

theorem K2_379_eq (h : ℤ) :
    K2_379 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (379 : ℤ) ∣ h then (54010153 / 54010152 : ℚ) else (20415837455 / 20415837456 : ℚ)) := by
  simp [K2_379, Kp_two h, Kp_threeHundredSeventyNine h]

end Brockian.Goldbach.WheelK2_379
