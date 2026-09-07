/-
  Brockian/GoldbachWheelK2_587.lean — exact local product K₂·K_587.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_587 from def: 1 ± 1/(p−1)^{3 or 4} with p=587 → (p−1)=586.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_587

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 587) := ⟨by decide⟩

theorem Kp_fiveHundredEightySeven_of_dvd {h : ℤ} (hh : (587 : ℤ) ∣ h) :
    Kp 587 h = (201230057 / 201230056 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredEightySeven_of_not_dvd {h : ℤ} (hh : ¬(587 : ℤ) ∣ h) :
    Kp 587 h = (117920812815 / 117920812816 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredEightySeven (h : ℤ) :
    Kp 587 h = if (587 : ℤ) ∣ h then (201230057 / 201230056 : ℚ) else (117920812815 / 117920812816 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredEightySeven_of_dvd hh
  · exact Kp_fiveHundredEightySeven_of_not_dvd hh

def K2_587 (h : ℤ) : ℚ := Kp 2 h * Kp 587 h

theorem K2_587_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_587 h = 0 := by
  simp [K2_587, Kp_two_of_not_dvd h2]

theorem K2_587_of_two_and_fiveHundredEightySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (587 : ℤ) ∣ h) :
    K2_587 h = (2 : ℚ) * (201230057 / 201230056) := by
  simp [K2_587, Kp_two_of_dvd h2, Kp_fiveHundredEightySeven_of_dvd hp]

theorem K2_587_eq (h : ℤ) :
    K2_587 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (587 : ℤ) ∣ h then (201230057 / 201230056 : ℚ) else (117920812815 / 117920812816 : ℚ)) := by
  simp [K2_587, Kp_two h, Kp_fiveHundredEightySeven h]

end Brockian.Goldbach.WheelK2_587
