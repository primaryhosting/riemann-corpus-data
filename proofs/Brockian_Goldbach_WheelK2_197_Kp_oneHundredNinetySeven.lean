/-
  Brockian/GoldbachWheelK2_197.lean — exact local product K₂·K_197.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_197 from def: 1 ± 1/(p−1)^{3 or 4} with p=197 → (p−1)=196.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_197

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 197) := ⟨by decide⟩

theorem Kp_oneHundredNinetySeven_of_dvd {h : ℤ} (hh : (197 : ℤ) ∣ h) :
    Kp 197 h = (7529537 / 7529536 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetySeven_of_not_dvd {h : ℤ} (hh : ¬(197 : ℤ) ∣ h) :
    Kp 197 h = (1475789055 / 1475789056 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetySeven (h : ℤ) :
    Kp 197 h = if (197 : ℤ) ∣ h then (7529537 / 7529536 : ℚ) else (1475789055 / 1475789056 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredNinetySeven_of_dvd hh
  · exact Kp_oneHundredNinetySeven_of_not_dvd hh

def K2_197 (h : ℤ) : ℚ := Kp 2 h * Kp 197 h

theorem K2_197_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_197 h = 0 := by
  simp [K2_197, Kp_two_of_not_dvd h2]

theorem K2_197_of_two_and_oneHundredNinetySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (197 : ℤ) ∣ h) :
    K2_197 h = (2 : ℚ) * (7529537 / 7529536) := by
  simp [K2_197, Kp_two_of_dvd h2, Kp_oneHundredNinetySeven_of_dvd hp]

theorem K2_197_eq (h : ℤ) :
    K2_197 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (197 : ℤ) ∣ h then (7529537 / 7529536 : ℚ) else (1475789055 / 1475789056 : ℚ)) := by
  simp [K2_197, Kp_two h, Kp_oneHundredNinetySeven h]

end Brockian.Goldbach.WheelK2_197
