/-
  Brockian/GoldbachWheelK2_569.lean — exact local product K₂·K_569.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_569 from def: 1 ± 1/(p−1)^{3 or 4} with p=569 → (p−1)=568.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_569

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 569) := ⟨by decide⟩

theorem Kp_fiveHundredSixtyNine_of_dvd {h : ℤ} (hh : (569 : ℤ) ∣ h) :
    Kp 569 h = (183250433 / 183250432 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredSixtyNine_of_not_dvd {h : ℤ} (hh : ¬(569 : ℤ) ∣ h) :
    Kp 569 h = (104086245375 / 104086245376 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredSixtyNine (h : ℤ) :
    Kp 569 h = if (569 : ℤ) ∣ h then (183250433 / 183250432 : ℚ) else (104086245375 / 104086245376 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredSixtyNine_of_dvd hh
  · exact Kp_fiveHundredSixtyNine_of_not_dvd hh

def K2_569 (h : ℤ) : ℚ := Kp 2 h * Kp 569 h

theorem K2_569_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_569 h = 0 := by
  simp [K2_569, Kp_two_of_not_dvd h2]

theorem K2_569_of_two_and_fiveHundredSixtyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (569 : ℤ) ∣ h) :
    K2_569 h = (2 : ℚ) * (183250433 / 183250432) := by
  simp [K2_569, Kp_two_of_dvd h2, Kp_fiveHundredSixtyNine_of_dvd hp]

theorem K2_569_eq (h : ℤ) :
    K2_569 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (569 : ℤ) ∣ h then (183250433 / 183250432 : ℚ) else (104086245375 / 104086245376 : ℚ)) := by
  simp [K2_569, Kp_two h, Kp_fiveHundredSixtyNine h]

end Brockian.Goldbach.WheelK2_569
