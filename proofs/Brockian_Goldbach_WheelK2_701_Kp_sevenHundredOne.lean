/-
  Brockian/GoldbachWheelK2_701.lean — exact local product K₂·K_701.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_701 from def: 1 ± 1/(p−1)^{3 or 4} with p=701 → (p−1)=700.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_701

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 701) := ⟨by decide⟩

theorem Kp_sevenHundredOne_of_dvd {h : ℤ} (hh : (701 : ℤ) ∣ h) :
    Kp 701 h = (343000001 / 343000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredOne_of_not_dvd {h : ℤ} (hh : ¬(701 : ℤ) ∣ h) :
    Kp 701 h = (240099999999 / 240100000000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredOne (h : ℤ) :
    Kp 701 h = if (701 : ℤ) ∣ h then (343000001 / 343000000 : ℚ) else (240099999999 / 240100000000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredOne_of_dvd hh
  · exact Kp_sevenHundredOne_of_not_dvd hh

def K2_701 (h : ℤ) : ℚ := Kp 2 h * Kp 701 h

theorem K2_701_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_701 h = 0 := by
  simp [K2_701, Kp_two_of_not_dvd h2]

theorem K2_701_of_two_and_sevenHundredOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (701 : ℤ) ∣ h) :
    K2_701 h = (2 : ℚ) * (343000001 / 343000000) := by
  simp [K2_701, Kp_two_of_dvd h2, Kp_sevenHundredOne_of_dvd hp]

theorem K2_701_eq (h : ℤ) :
    K2_701 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (701 : ℤ) ∣ h then (343000001 / 343000000 : ℚ) else (240099999999 / 240100000000 : ℚ)) := by
  simp [K2_701, Kp_two h, Kp_sevenHundredOne h]

end Brockian.Goldbach.WheelK2_701
