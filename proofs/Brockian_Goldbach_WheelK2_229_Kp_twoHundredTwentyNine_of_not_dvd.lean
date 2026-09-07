/-
  Brockian/GoldbachWheelK2_229.lean — exact local product K₂·K_229.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_229 from def: 1 ± 1/(p−1)^{3 or 4} with p=229 → (p−1)=228.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_229

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 229) := ⟨by decide⟩

theorem Kp_twoHundredTwentyNine_of_dvd {h : ℤ} (hh : (229 : ℤ) ∣ h) :
    Kp 229 h = (11852353 / 11852352 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredTwentyNine_of_not_dvd {h : ℤ} (hh : ¬(229 : ℤ) ∣ h) :
    Kp 229 h = (2702336255 / 2702336256 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredTwentyNine (h : ℤ) :
    Kp 229 h = if (229 : ℤ) ∣ h then (11852353 / 11852352 : ℚ) else (2702336255 / 2702336256 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredTwentyNine_of_dvd hh
  · exact Kp_twoHundredTwentyNine_of_not_dvd hh

def K2_229 (h : ℤ) : ℚ := Kp 2 h * Kp 229 h

theorem K2_229_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_229 h = 0 := by
  simp [K2_229, Kp_two_of_not_dvd h2]

theorem K2_229_of_two_and_twoHundredTwentyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (229 : ℤ) ∣ h) :
    K2_229 h = (2 : ℚ) * (11852353 / 11852352) := by
  simp [K2_229, Kp_two_of_dvd h2, Kp_twoHundredTwentyNine_of_dvd hp]

theorem K2_229_eq (h : ℤ) :
    K2_229 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (229 : ℤ) ∣ h then (11852353 / 11852352 : ℚ) else (2702336255 / 2702336256 : ℚ)) := by
  simp [K2_229, Kp_two h, Kp_twoHundredTwentyNine h]

end Brockian.Goldbach.WheelK2_229
