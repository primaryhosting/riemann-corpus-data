/-
  Brockian/GoldbachWheelK2_757.lean — exact local product K₂·K_757.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_757 from def: 1 ± 1/(p−1)^{3 or 4} with p=757 → (p−1)=756.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_757

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 757) := ⟨by decide⟩

theorem Kp_sevenHundredFiftySeven_of_dvd {h : ℤ} (hh : (757 : ℤ) ∣ h) :
    Kp 757 h = (432081217 / 432081216 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredFiftySeven_of_not_dvd {h : ℤ} (hh : ¬(757 : ℤ) ∣ h) :
    Kp 757 h = (326653399295 / 326653399296 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredFiftySeven (h : ℤ) :
    Kp 757 h = if (757 : ℤ) ∣ h then (432081217 / 432081216 : ℚ) else (326653399295 / 326653399296 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredFiftySeven_of_dvd hh
  · exact Kp_sevenHundredFiftySeven_of_not_dvd hh

def K2_757 (h : ℤ) : ℚ := Kp 2 h * Kp 757 h

theorem K2_757_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_757 h = 0 := by
  simp [K2_757, Kp_two_of_not_dvd h2]

theorem K2_757_of_two_and_sevenHundredFiftySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (757 : ℤ) ∣ h) :
    K2_757 h = (2 : ℚ) * (432081217 / 432081216) := by
  simp [K2_757, Kp_two_of_dvd h2, Kp_sevenHundredFiftySeven_of_dvd hp]

theorem K2_757_eq (h : ℤ) :
    K2_757 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (757 : ℤ) ∣ h then (432081217 / 432081216 : ℚ) else (326653399295 / 326653399296 : ℚ)) := by
  simp [K2_757, Kp_two h, Kp_sevenHundredFiftySeven h]

end Brockian.Goldbach.WheelK2_757
