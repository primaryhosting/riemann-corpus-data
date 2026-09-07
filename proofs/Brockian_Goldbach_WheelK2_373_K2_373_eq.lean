/-
  Brockian/GoldbachWheelK2_373.lean — exact local product K₂·K_373.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_373 from def: 1 ± 1/(p−1)^{3 or 4} with p=373 → (p−1)=372.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_373

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 373) := ⟨by decide⟩

theorem Kp_threeHundredSeventyThree_of_dvd {h : ℤ} (hh : (373 : ℤ) ∣ h) :
    Kp 373 h = (51478849 / 51478848 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeventyThree_of_not_dvd {h : ℤ} (hh : ¬(373 : ℤ) ∣ h) :
    Kp 373 h = (19150131455 / 19150131456 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredSeventyThree (h : ℤ) :
    Kp 373 h = if (373 : ℤ) ∣ h then (51478849 / 51478848 : ℚ) else (19150131455 / 19150131456 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredSeventyThree_of_dvd hh
  · exact Kp_threeHundredSeventyThree_of_not_dvd hh

def K2_373 (h : ℤ) : ℚ := Kp 2 h * Kp 373 h

theorem K2_373_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_373 h = 0 := by
  simp [K2_373, Kp_two_of_not_dvd h2]

theorem K2_373_of_two_and_threeHundredSeventyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (373 : ℤ) ∣ h) :
    K2_373 h = (2 : ℚ) * (51478849 / 51478848) := by
  simp [K2_373, Kp_two_of_dvd h2, Kp_threeHundredSeventyThree_of_dvd hp]

theorem K2_373_eq (h : ℤ) :
    K2_373 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (373 : ℤ) ∣ h then (51478849 / 51478848 : ℚ) else (19150131455 / 19150131456 : ℚ)) := by
  simp [K2_373, Kp_two h, Kp_threeHundredSeventyThree h]

end Brockian.Goldbach.WheelK2_373
