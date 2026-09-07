/-
  Brockian/GoldbachWheelK2_631.lean — exact local product K₂·K_631.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_631 from def: 1 ± 1/(p−1)^{3 or 4} with p=631 → (p−1)=630.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_631

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 631) := ⟨by decide⟩

theorem Kp_sixHundredThirtyOne_of_dvd {h : ℤ} (hh : (631 : ℤ) ∣ h) :
    Kp 631 h = (250047001 / 250047000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredThirtyOne_of_not_dvd {h : ℤ} (hh : ¬(631 : ℤ) ∣ h) :
    Kp 631 h = (157529609999 / 157529610000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredThirtyOne (h : ℤ) :
    Kp 631 h = if (631 : ℤ) ∣ h then (250047001 / 250047000 : ℚ) else (157529609999 / 157529610000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredThirtyOne_of_dvd hh
  · exact Kp_sixHundredThirtyOne_of_not_dvd hh

def K2_631 (h : ℤ) : ℚ := Kp 2 h * Kp 631 h

theorem K2_631_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_631 h = 0 := by
  simp [K2_631, Kp_two_of_not_dvd h2]

theorem K2_631_of_two_and_sixHundredThirtyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (631 : ℤ) ∣ h) :
    K2_631 h = (2 : ℚ) * (250047001 / 250047000) := by
  simp [K2_631, Kp_two_of_dvd h2, Kp_sixHundredThirtyOne_of_dvd hp]

theorem K2_631_eq (h : ℤ) :
    K2_631 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (631 : ℤ) ∣ h then (250047001 / 250047000 : ℚ) else (157529609999 / 157529610000 : ℚ)) := by
  simp [K2_631, Kp_two h, Kp_sixHundredThirtyOne h]

end Brockian.Goldbach.WheelK2_631
