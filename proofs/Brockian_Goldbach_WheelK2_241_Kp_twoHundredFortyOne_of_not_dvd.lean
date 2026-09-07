/-
  Brockian/GoldbachWheelK2_241.lean — exact local product K₂·K_241.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_241 from def: 1 ± 1/(p−1)^{3 or 4} with p=241 → (p−1)=240.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_241

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 241) := ⟨by decide⟩

theorem Kp_twoHundredFortyOne_of_dvd {h : ℤ} (hh : (241 : ℤ) ∣ h) :
    Kp 241 h = (13824001 / 13824000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredFortyOne_of_not_dvd {h : ℤ} (hh : ¬(241 : ℤ) ∣ h) :
    Kp 241 h = (3317759999 / 3317760000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredFortyOne (h : ℤ) :
    Kp 241 h = if (241 : ℤ) ∣ h then (13824001 / 13824000 : ℚ) else (3317759999 / 3317760000 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredFortyOne_of_dvd hh
  · exact Kp_twoHundredFortyOne_of_not_dvd hh

def K2_241 (h : ℤ) : ℚ := Kp 2 h * Kp 241 h

theorem K2_241_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_241 h = 0 := by
  simp [K2_241, Kp_two_of_not_dvd h2]

theorem K2_241_of_two_and_twoHundredFortyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (241 : ℤ) ∣ h) :
    K2_241 h = (2 : ℚ) * (13824001 / 13824000) := by
  simp [K2_241, Kp_two_of_dvd h2, Kp_twoHundredFortyOne_of_dvd hp]

theorem K2_241_eq (h : ℤ) :
    K2_241 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (241 : ℤ) ∣ h then (13824001 / 13824000 : ℚ) else (3317759999 / 3317760000 : ℚ)) := by
  simp [K2_241, Kp_two h, Kp_twoHundredFortyOne h]

end Brockian.Goldbach.WheelK2_241
