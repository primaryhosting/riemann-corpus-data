/-
  Brockian/GoldbachWheelK2_347.lean — exact local product K₂·K_347.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_347 from def: 1 ± 1/(p−1)^{3 or 4} with p=347 → (p−1)=346.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_347

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 347) := ⟨by decide⟩

theorem Kp_threeHundredFortySeven_of_dvd {h : ℤ} (hh : (347 : ℤ) ∣ h) :
    Kp 347 h = (41421737 / 41421736 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFortySeven_of_not_dvd {h : ℤ} (hh : ¬(347 : ℤ) ∣ h) :
    Kp 347 h = (14331920655 / 14331920656 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredFortySeven (h : ℤ) :
    Kp 347 h = if (347 : ℤ) ∣ h then (41421737 / 41421736 : ℚ) else (14331920655 / 14331920656 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredFortySeven_of_dvd hh
  · exact Kp_threeHundredFortySeven_of_not_dvd hh

def K2_347 (h : ℤ) : ℚ := Kp 2 h * Kp 347 h

theorem K2_347_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_347 h = 0 := by
  simp [K2_347, Kp_two_of_not_dvd h2]

theorem K2_347_of_two_and_threeHundredFortySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (347 : ℤ) ∣ h) :
    K2_347 h = (2 : ℚ) * (41421737 / 41421736) := by
  simp [K2_347, Kp_two_of_dvd h2, Kp_threeHundredFortySeven_of_dvd hp]

theorem K2_347_eq (h : ℤ) :
    K2_347 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (347 : ℤ) ∣ h then (41421737 / 41421736 : ℚ) else (14331920655 / 14331920656 : ℚ)) := by
  simp [K2_347, Kp_two h, Kp_threeHundredFortySeven h]

end Brockian.Goldbach.WheelK2_347
