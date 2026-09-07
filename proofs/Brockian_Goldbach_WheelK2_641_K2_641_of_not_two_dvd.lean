/-
  Brockian/GoldbachWheelK2_641.lean — exact local product K₂·K_641.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_641 from def: 1 ± 1/(p−1)^{3 or 4} with p=641 → (p−1)=640.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_641

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 641) := ⟨by decide⟩

theorem Kp_sixHundredFortyOne_of_dvd {h : ℤ} (hh : (641 : ℤ) ∣ h) :
    Kp 641 h = (262144001 / 262144000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFortyOne_of_not_dvd {h : ℤ} (hh : ¬(641 : ℤ) ∣ h) :
    Kp 641 h = (167772159999 / 167772160000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFortyOne (h : ℤ) :
    Kp 641 h = if (641 : ℤ) ∣ h then (262144001 / 262144000 : ℚ) else (167772159999 / 167772160000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredFortyOne_of_dvd hh
  · exact Kp_sixHundredFortyOne_of_not_dvd hh

def K2_641 (h : ℤ) : ℚ := Kp 2 h * Kp 641 h

theorem K2_641_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_641 h = 0 := by
  simp [K2_641, Kp_two_of_not_dvd h2]

theorem K2_641_of_two_and_sixHundredFortyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (641 : ℤ) ∣ h) :
    K2_641 h = (2 : ℚ) * (262144001 / 262144000) := by
  simp [K2_641, Kp_two_of_dvd h2, Kp_sixHundredFortyOne_of_dvd hp]

theorem K2_641_eq (h : ℤ) :
    K2_641 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (641 : ℤ) ∣ h then (262144001 / 262144000 : ℚ) else (167772159999 / 167772160000 : ℚ)) := by
  simp [K2_641, Kp_two h, Kp_sixHundredFortyOne h]

end Brockian.Goldbach.WheelK2_641
