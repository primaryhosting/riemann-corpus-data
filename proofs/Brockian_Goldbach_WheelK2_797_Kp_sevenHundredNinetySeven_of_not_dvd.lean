/-
  Brockian/GoldbachWheelK2_797.lean — exact local product K₂·K_797.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_797 from def: 1 ± 1/(p−1)^{3 or 4} with p=797 → (p−1)=796.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_797

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 797) := ⟨by decide⟩

theorem Kp_sevenHundredNinetySeven_of_dvd {h : ℤ} (hh : (797 : ℤ) ∣ h) :
    Kp 797 h = (504358337 / 504358336 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredNinetySeven_of_not_dvd {h : ℤ} (hh : ¬(797 : ℤ) ∣ h) :
    Kp 797 h = (401469235455 / 401469235456 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredNinetySeven (h : ℤ) :
    Kp 797 h = if (797 : ℤ) ∣ h then (504358337 / 504358336 : ℚ) else (401469235455 / 401469235456 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredNinetySeven_of_dvd hh
  · exact Kp_sevenHundredNinetySeven_of_not_dvd hh

def K2_797 (h : ℤ) : ℚ := Kp 2 h * Kp 797 h

theorem K2_797_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_797 h = 0 := by
  simp [K2_797, Kp_two_of_not_dvd h2]

theorem K2_797_of_two_and_sevenHundredNinetySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (797 : ℤ) ∣ h) :
    K2_797 h = (2 : ℚ) * (504358337 / 504358336) := by
  simp [K2_797, Kp_two_of_dvd h2, Kp_sevenHundredNinetySeven_of_dvd hp]

theorem K2_797_eq (h : ℤ) :
    K2_797 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (797 : ℤ) ∣ h then (504358337 / 504358336 : ℚ) else (401469235455 / 401469235456 : ℚ)) := by
  simp [K2_797, Kp_two h, Kp_sevenHundredNinetySeven h]

end Brockian.Goldbach.WheelK2_797
