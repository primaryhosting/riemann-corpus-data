/-
  Brockian/GoldbachWheelK2_457.lean — exact local product K₂·K_457.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_457 from def: 1 ± 1/(p−1)^{3 or 4} with p=457 → (p−1)=456.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_457

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 457) := ⟨by decide⟩

theorem Kp_fourHundredFiftySeven_of_dvd {h : ℤ} (hh : (457 : ℤ) ∣ h) :
    Kp 457 h = (94818817 / 94818816 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredFiftySeven_of_not_dvd {h : ℤ} (hh : ¬(457 : ℤ) ∣ h) :
    Kp 457 h = (43237380095 / 43237380096 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredFiftySeven (h : ℤ) :
    Kp 457 h = if (457 : ℤ) ∣ h then (94818817 / 94818816 : ℚ) else (43237380095 / 43237380096 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredFiftySeven_of_dvd hh
  · exact Kp_fourHundredFiftySeven_of_not_dvd hh

def K2_457 (h : ℤ) : ℚ := Kp 2 h * Kp 457 h

theorem K2_457_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_457 h = 0 := by
  simp [K2_457, Kp_two_of_not_dvd h2]

theorem K2_457_of_two_and_fourHundredFiftySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (457 : ℤ) ∣ h) :
    K2_457 h = (2 : ℚ) * (94818817 / 94818816) := by
  simp [K2_457, Kp_two_of_dvd h2, Kp_fourHundredFiftySeven_of_dvd hp]

theorem K2_457_eq (h : ℤ) :
    K2_457 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (457 : ℤ) ∣ h then (94818817 / 94818816 : ℚ) else (43237380095 / 43237380096 : ℚ)) := by
  simp [K2_457, Kp_two h, Kp_fourHundredFiftySeven h]

end Brockian.Goldbach.WheelK2_457
