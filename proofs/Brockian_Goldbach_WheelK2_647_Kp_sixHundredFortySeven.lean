/-
  Brockian/GoldbachWheelK2_647.lean — exact local product K₂·K_647.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_647 from def: 1 ± 1/(p−1)^{3 or 4} with p=647 → (p−1)=646.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_647

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 647) := ⟨by decide⟩

theorem Kp_sixHundredFortySeven_of_dvd {h : ℤ} (hh : (647 : ℤ) ∣ h) :
    Kp 647 h = (269586137 / 269586136 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFortySeven_of_not_dvd {h : ℤ} (hh : ¬(647 : ℤ) ∣ h) :
    Kp 647 h = (174152643855 / 174152643856 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFortySeven (h : ℤ) :
    Kp 647 h = if (647 : ℤ) ∣ h then (269586137 / 269586136 : ℚ) else (174152643855 / 174152643856 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredFortySeven_of_dvd hh
  · exact Kp_sixHundredFortySeven_of_not_dvd hh

def K2_647 (h : ℤ) : ℚ := Kp 2 h * Kp 647 h

theorem K2_647_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_647 h = 0 := by
  simp [K2_647, Kp_two_of_not_dvd h2]

theorem K2_647_of_two_and_sixHundredFortySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (647 : ℤ) ∣ h) :
    K2_647 h = (2 : ℚ) * (269586137 / 269586136) := by
  simp [K2_647, Kp_two_of_dvd h2, Kp_sixHundredFortySeven_of_dvd hp]

theorem K2_647_eq (h : ℤ) :
    K2_647 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (647 : ℤ) ∣ h then (269586137 / 269586136 : ℚ) else (174152643855 / 174152643856 : ℚ)) := by
  simp [K2_647, Kp_two h, Kp_sixHundredFortySeven h]

end Brockian.Goldbach.WheelK2_647
