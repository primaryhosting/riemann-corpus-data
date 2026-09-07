/-
  Brockian/GoldbachWheelK2_251.lean — exact local product K₂·K_251.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_251 from def: 1 ± 1/(p−1)^{3 or 4} with p=251 → (p−1)=250.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_251

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 251) := ⟨by decide⟩

theorem Kp_twoHundredFiftyOne_of_dvd {h : ℤ} (hh : (251 : ℤ) ∣ h) :
    Kp 251 h = (15625001 / 15625000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredFiftyOne_of_not_dvd {h : ℤ} (hh : ¬(251 : ℤ) ∣ h) :
    Kp 251 h = (3906249999 / 3906250000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredFiftyOne (h : ℤ) :
    Kp 251 h = if (251 : ℤ) ∣ h then (15625001 / 15625000 : ℚ) else (3906249999 / 3906250000 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredFiftyOne_of_dvd hh
  · exact Kp_twoHundredFiftyOne_of_not_dvd hh

def K2_251 (h : ℤ) : ℚ := Kp 2 h * Kp 251 h

theorem K2_251_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_251 h = 0 := by
  simp [K2_251, Kp_two_of_not_dvd h2]

theorem K2_251_of_two_and_twoHundredFiftyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (251 : ℤ) ∣ h) :
    K2_251 h = (2 : ℚ) * (15625001 / 15625000) := by
  simp [K2_251, Kp_two_of_dvd h2, Kp_twoHundredFiftyOne_of_dvd hp]

theorem K2_251_eq (h : ℤ) :
    K2_251 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (251 : ℤ) ∣ h then (15625001 / 15625000 : ℚ) else (3906249999 / 3906250000 : ℚ)) := by
  simp [K2_251, Kp_two h, Kp_twoHundredFiftyOne h]

end Brockian.Goldbach.WheelK2_251
