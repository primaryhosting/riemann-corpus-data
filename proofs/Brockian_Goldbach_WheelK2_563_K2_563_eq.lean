/-
  Brockian/GoldbachWheelK2_563.lean — exact local product K₂·K_563.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_563 from def: 1 ± 1/(p−1)^{3 or 4} with p=563 → (p−1)=562.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_563

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 563) := ⟨by decide⟩

theorem Kp_fiveHundredSixtyThree_of_dvd {h : ℤ} (hh : (563 : ℤ) ∣ h) :
    Kp 563 h = (177504329 / 177504328 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredSixtyThree_of_not_dvd {h : ℤ} (hh : ¬(563 : ℤ) ∣ h) :
    Kp 563 h = (99757432335 / 99757432336 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredSixtyThree (h : ℤ) :
    Kp 563 h = if (563 : ℤ) ∣ h then (177504329 / 177504328 : ℚ) else (99757432335 / 99757432336 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredSixtyThree_of_dvd hh
  · exact Kp_fiveHundredSixtyThree_of_not_dvd hh

def K2_563 (h : ℤ) : ℚ := Kp 2 h * Kp 563 h

theorem K2_563_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_563 h = 0 := by
  simp [K2_563, Kp_two_of_not_dvd h2]

theorem K2_563_of_two_and_fiveHundredSixtyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (563 : ℤ) ∣ h) :
    K2_563 h = (2 : ℚ) * (177504329 / 177504328) := by
  simp [K2_563, Kp_two_of_dvd h2, Kp_fiveHundredSixtyThree_of_dvd hp]

theorem K2_563_eq (h : ℤ) :
    K2_563 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (563 : ℤ) ∣ h then (177504329 / 177504328 : ℚ) else (99757432335 / 99757432336 : ℚ)) := by
  simp [K2_563, Kp_two h, Kp_fiveHundredSixtyThree h]

end Brockian.Goldbach.WheelK2_563
