/-
  Brockian/GoldbachWheelK2_547.lean — exact local product K₂·K_547.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_547 from def: 1 ± 1/(p−1)^{3 or 4} with p=547 → (p−1)=546.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_547

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 547) := ⟨by decide⟩

theorem Kp_fiveHundredFortySeven_of_dvd {h : ℤ} (hh : (547 : ℤ) ∣ h) :
    Kp 547 h = (162771337 / 162771336 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredFortySeven_of_not_dvd {h : ℤ} (hh : ¬(547 : ℤ) ∣ h) :
    Kp 547 h = (88873149455 / 88873149456 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredFortySeven (h : ℤ) :
    Kp 547 h = if (547 : ℤ) ∣ h then (162771337 / 162771336 : ℚ) else (88873149455 / 88873149456 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredFortySeven_of_dvd hh
  · exact Kp_fiveHundredFortySeven_of_not_dvd hh

def K2_547 (h : ℤ) : ℚ := Kp 2 h * Kp 547 h

theorem K2_547_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_547 h = 0 := by
  simp [K2_547, Kp_two_of_not_dvd h2]

theorem K2_547_of_two_and_fiveHundredFortySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (547 : ℤ) ∣ h) :
    K2_547 h = (2 : ℚ) * (162771337 / 162771336) := by
  simp [K2_547, Kp_two_of_dvd h2, Kp_fiveHundredFortySeven_of_dvd hp]

theorem K2_547_eq (h : ℤ) :
    K2_547 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (547 : ℤ) ∣ h then (162771337 / 162771336 : ℚ) else (88873149455 / 88873149456 : ℚ)) := by
  simp [K2_547, Kp_two h, Kp_fiveHundredFortySeven h]

end Brockian.Goldbach.WheelK2_547
