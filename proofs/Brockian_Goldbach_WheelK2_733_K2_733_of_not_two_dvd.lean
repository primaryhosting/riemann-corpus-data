/-
  Brockian/GoldbachWheelK2_733.lean — exact local product K₂·K_733.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_733 from def: 1 ± 1/(p−1)^{3 or 4} with p=733 → (p−1)=732.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_733

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 733) := ⟨by decide⟩

theorem Kp_sevenHundredThirtyThree_of_dvd {h : ℤ} (hh : (733 : ℤ) ∣ h) :
    Kp 733 h = (392223169 / 392223168 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredThirtyThree_of_not_dvd {h : ℤ} (hh : ¬(733 : ℤ) ∣ h) :
    Kp 733 h = (287107358975 / 287107358976 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredThirtyThree (h : ℤ) :
    Kp 733 h = if (733 : ℤ) ∣ h then (392223169 / 392223168 : ℚ) else (287107358975 / 287107358976 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredThirtyThree_of_dvd hh
  · exact Kp_sevenHundredThirtyThree_of_not_dvd hh

def K2_733 (h : ℤ) : ℚ := Kp 2 h * Kp 733 h

theorem K2_733_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_733 h = 0 := by
  simp [K2_733, Kp_two_of_not_dvd h2]

theorem K2_733_of_two_and_sevenHundredThirtyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (733 : ℤ) ∣ h) :
    K2_733 h = (2 : ℚ) * (392223169 / 392223168) := by
  simp [K2_733, Kp_two_of_dvd h2, Kp_sevenHundredThirtyThree_of_dvd hp]

theorem K2_733_eq (h : ℤ) :
    K2_733 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (733 : ℤ) ∣ h then (392223169 / 392223168 : ℚ) else (287107358975 / 287107358976 : ℚ)) := by
  simp [K2_733, Kp_two h, Kp_sevenHundredThirtyThree h]

end Brockian.Goldbach.WheelK2_733
