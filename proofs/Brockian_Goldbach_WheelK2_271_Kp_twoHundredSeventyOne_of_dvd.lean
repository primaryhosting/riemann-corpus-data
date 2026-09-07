/-
  Brockian/GoldbachWheelK2_271.lean — exact local product K₂·K_271.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_271 from def: 1 ± 1/(p−1)^{3 or 4} with p=271 → (p−1)=270.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_271

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 271) := ⟨by decide⟩

theorem Kp_twoHundredSeventyOne_of_dvd {h : ℤ} (hh : (271 : ℤ) ∣ h) :
    Kp 271 h = (19683001 / 19683000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSeventyOne_of_not_dvd {h : ℤ} (hh : ¬(271 : ℤ) ∣ h) :
    Kp 271 h = (5314409999 / 5314410000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredSeventyOne (h : ℤ) :
    Kp 271 h = if (271 : ℤ) ∣ h then (19683001 / 19683000 : ℚ) else (5314409999 / 5314410000 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredSeventyOne_of_dvd hh
  · exact Kp_twoHundredSeventyOne_of_not_dvd hh

def K2_271 (h : ℤ) : ℚ := Kp 2 h * Kp 271 h

theorem K2_271_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_271 h = 0 := by
  simp [K2_271, Kp_two_of_not_dvd h2]

theorem K2_271_of_two_and_twoHundredSeventyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (271 : ℤ) ∣ h) :
    K2_271 h = (2 : ℚ) * (19683001 / 19683000) := by
  simp [K2_271, Kp_two_of_dvd h2, Kp_twoHundredSeventyOne_of_dvd hp]

theorem K2_271_eq (h : ℤ) :
    K2_271 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (271 : ℤ) ∣ h then (19683001 / 19683000 : ℚ) else (5314409999 / 5314410000 : ℚ)) := by
  simp [K2_271, Kp_two h, Kp_twoHundredSeventyOne h]

end Brockian.Goldbach.WheelK2_271
