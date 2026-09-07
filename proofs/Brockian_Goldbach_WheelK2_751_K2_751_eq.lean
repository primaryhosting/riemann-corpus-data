/-
  Brockian/GoldbachWheelK2_751.lean — exact local product K₂·K_751.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_751 from def: 1 ± 1/(p−1)^{3 or 4} with p=751 → (p−1)=750.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_751

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 751) := ⟨by decide⟩

theorem Kp_sevenHundredFiftyOne_of_dvd {h : ℤ} (hh : (751 : ℤ) ∣ h) :
    Kp 751 h = (421875001 / 421875000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredFiftyOne_of_not_dvd {h : ℤ} (hh : ¬(751 : ℤ) ∣ h) :
    Kp 751 h = (316406249999 / 316406250000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredFiftyOne (h : ℤ) :
    Kp 751 h = if (751 : ℤ) ∣ h then (421875001 / 421875000 : ℚ) else (316406249999 / 316406250000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredFiftyOne_of_dvd hh
  · exact Kp_sevenHundredFiftyOne_of_not_dvd hh

def K2_751 (h : ℤ) : ℚ := Kp 2 h * Kp 751 h

theorem K2_751_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_751 h = 0 := by
  simp [K2_751, Kp_two_of_not_dvd h2]

theorem K2_751_of_two_and_sevenHundredFiftyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (751 : ℤ) ∣ h) :
    K2_751 h = (2 : ℚ) * (421875001 / 421875000) := by
  simp [K2_751, Kp_two_of_dvd h2, Kp_sevenHundredFiftyOne_of_dvd hp]

theorem K2_751_eq (h : ℤ) :
    K2_751 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (751 : ℤ) ∣ h then (421875001 / 421875000 : ℚ) else (316406249999 / 316406250000 : ℚ)) := by
  simp [K2_751, Kp_two h, Kp_sevenHundredFiftyOne h]

end Brockian.Goldbach.WheelK2_751
