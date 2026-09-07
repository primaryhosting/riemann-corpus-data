/-
  Brockian/GoldbachWheelK2_673.lean — exact local product K₂·K_673.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_673 from def: 1 ± 1/(p−1)^{3 or 4} with p=673 → (p−1)=672.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_673

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 673) := ⟨by decide⟩

theorem Kp_sixHundredSeventyThree_of_dvd {h : ℤ} (hh : (673 : ℤ) ∣ h) :
    Kp 673 h = (303464449 / 303464448 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeventyThree_of_not_dvd {h : ℤ} (hh : ¬(673 : ℤ) ∣ h) :
    Kp 673 h = (203928109055 / 203928109056 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeventyThree (h : ℤ) :
    Kp 673 h = if (673 : ℤ) ∣ h then (303464449 / 303464448 : ℚ) else (203928109055 / 203928109056 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredSeventyThree_of_dvd hh
  · exact Kp_sixHundredSeventyThree_of_not_dvd hh

def K2_673 (h : ℤ) : ℚ := Kp 2 h * Kp 673 h

theorem K2_673_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_673 h = 0 := by
  simp [K2_673, Kp_two_of_not_dvd h2]

theorem K2_673_of_two_and_sixHundredSeventyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (673 : ℤ) ∣ h) :
    K2_673 h = (2 : ℚ) * (303464449 / 303464448) := by
  simp [K2_673, Kp_two_of_dvd h2, Kp_sixHundredSeventyThree_of_dvd hp]

theorem K2_673_eq (h : ℤ) :
    K2_673 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (673 : ℤ) ∣ h then (303464449 / 303464448 : ℚ) else (203928109055 / 203928109056 : ℚ)) := by
  simp [K2_673, Kp_two h, Kp_sixHundredSeventyThree h]

end Brockian.Goldbach.WheelK2_673
