/-
  Brockian/GoldbachWheelK2_643.lean — exact local product K₂·K_643.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_643 from def: 1 ± 1/(p−1)^{3 or 4} with p=643 → (p−1)=642.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_643

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 643) := ⟨by decide⟩

theorem Kp_sixHundredFortyThree_of_dvd {h : ℤ} (hh : (643 : ℤ) ∣ h) :
    Kp 643 h = (264609289 / 264609288 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFortyThree_of_not_dvd {h : ℤ} (hh : ¬(643 : ℤ) ∣ h) :
    Kp 643 h = (169879162895 / 169879162896 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFortyThree (h : ℤ) :
    Kp 643 h = if (643 : ℤ) ∣ h then (264609289 / 264609288 : ℚ) else (169879162895 / 169879162896 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredFortyThree_of_dvd hh
  · exact Kp_sixHundredFortyThree_of_not_dvd hh

def K2_643 (h : ℤ) : ℚ := Kp 2 h * Kp 643 h

theorem K2_643_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_643 h = 0 := by
  simp [K2_643, Kp_two_of_not_dvd h2]

theorem K2_643_of_two_and_sixHundredFortyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (643 : ℤ) ∣ h) :
    K2_643 h = (2 : ℚ) * (264609289 / 264609288) := by
  simp [K2_643, Kp_two_of_dvd h2, Kp_sixHundredFortyThree_of_dvd hp]

theorem K2_643_eq (h : ℤ) :
    K2_643 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (643 : ℤ) ∣ h then (264609289 / 264609288 : ℚ) else (169879162895 / 169879162896 : ℚ)) := by
  simp [K2_643, Kp_two h, Kp_sixHundredFortyThree h]

end Brockian.Goldbach.WheelK2_643
