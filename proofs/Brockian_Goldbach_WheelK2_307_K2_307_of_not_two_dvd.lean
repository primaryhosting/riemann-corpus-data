/-
  Brockian/GoldbachWheelK2_307.lean — exact local product K₂·K_307.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_307 from def: 1 ± 1/(p−1)^{3 or 4} with p=307 → (p−1)=306.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_307

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 307) := ⟨by decide⟩

theorem Kp_threeHundredSeven_of_dvd {h : ℤ} (hh : (307 : ℤ) ∣ h) :
    Kp 307 h = (28652617 / 28652616 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeven_of_not_dvd {h : ℤ} (hh : ¬(307 : ℤ) ∣ h) :
    Kp 307 h = (8767700495 / 8767700496 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeven (h : ℤ) :
    Kp 307 h = if (307 : ℤ) ∣ h then (28652617 / 28652616 : ℚ) else (8767700495 / 8767700496 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredSeven_of_dvd hh
  · exact Kp_threeHundredSeven_of_not_dvd hh

def K2_307 (h : ℤ) : ℚ := Kp 2 h * Kp 307 h

theorem K2_307_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_307 h = 0 := by
  simp [K2_307, Kp_two_of_not_dvd h2]

theorem K2_307_of_two_and_threeHundredSeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (307 : ℤ) ∣ h) :
    K2_307 h = (2 : ℚ) * (28652617 / 28652616) := by
  simp [K2_307, Kp_two_of_dvd h2, Kp_threeHundredSeven_of_dvd hp]

theorem K2_307_eq (h : ℤ) :
    K2_307 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (307 : ℤ) ∣ h then (28652617 / 28652616 : ℚ) else (8767700495 / 8767700496 : ℚ)) := by
  simp [K2_307, Kp_two h, Kp_threeHundredSeven h]

end Brockian.Goldbach.WheelK2_307
