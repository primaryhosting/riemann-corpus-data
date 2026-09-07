/-
  Brockian/GoldbachWheelK2_503.lean — exact local product K₂·K_503.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_503 from def: 1 ± 1/(p−1)^{3 or 4} with p=503 → (p−1)=502.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_503

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 503) := ⟨by decide⟩

theorem Kp_fiveHundredThree_of_dvd {h : ℤ} (hh : (503 : ℤ) ∣ h) :
    Kp 503 h = (126506009 / 126506008 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredThree_of_not_dvd {h : ℤ} (hh : ¬(503 : ℤ) ∣ h) :
    Kp 503 h = (63506016015 / 63506016016 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredThree (h : ℤ) :
    Kp 503 h = if (503 : ℤ) ∣ h then (126506009 / 126506008 : ℚ) else (63506016015 / 63506016016 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredThree_of_dvd hh
  · exact Kp_fiveHundredThree_of_not_dvd hh

def K2_503 (h : ℤ) : ℚ := Kp 2 h * Kp 503 h

theorem K2_503_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_503 h = 0 := by
  simp [K2_503, Kp_two_of_not_dvd h2]

theorem K2_503_of_two_and_fiveHundredThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (503 : ℤ) ∣ h) :
    K2_503 h = (2 : ℚ) * (126506009 / 126506008) := by
  simp [K2_503, Kp_two_of_dvd h2, Kp_fiveHundredThree_of_dvd hp]

theorem K2_503_eq (h : ℤ) :
    K2_503 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (503 : ℤ) ∣ h then (126506009 / 126506008 : ℚ) else (63506016015 / 63506016016 : ℚ)) := by
  simp [K2_503, Kp_two h, Kp_fiveHundredThree h]

end Brockian.Goldbach.WheelK2_503
