/-
  Brockian/GoldbachWheelK2_439.lean — exact local product K₂·K_439.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_439 from def: 1 ± 1/(p−1)^{3 or 4} with p=439 → (p−1)=438.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_439

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 439) := ⟨by decide⟩

theorem Kp_fourHundredThirtyNine_of_dvd {h : ℤ} (hh : (439 : ℤ) ∣ h) :
    Kp 439 h = (84027673 / 84027672 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredThirtyNine_of_not_dvd {h : ℤ} (hh : ¬(439 : ℤ) ∣ h) :
    Kp 439 h = (36804120335 / 36804120336 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredThirtyNine (h : ℤ) :
    Kp 439 h = if (439 : ℤ) ∣ h then (84027673 / 84027672 : ℚ) else (36804120335 / 36804120336 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredThirtyNine_of_dvd hh
  · exact Kp_fourHundredThirtyNine_of_not_dvd hh

def K2_439 (h : ℤ) : ℚ := Kp 2 h * Kp 439 h

theorem K2_439_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_439 h = 0 := by
  simp [K2_439, Kp_two_of_not_dvd h2]

theorem K2_439_of_two_and_fourHundredThirtyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (439 : ℤ) ∣ h) :
    K2_439 h = (2 : ℚ) * (84027673 / 84027672) := by
  simp [K2_439, Kp_two_of_dvd h2, Kp_fourHundredThirtyNine_of_dvd hp]

theorem K2_439_eq (h : ℤ) :
    K2_439 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (439 : ℤ) ∣ h then (84027673 / 84027672 : ℚ) else (36804120335 / 36804120336 : ℚ)) := by
  simp [K2_439, Kp_two h, Kp_fourHundredThirtyNine h]

end Brockian.Goldbach.WheelK2_439
