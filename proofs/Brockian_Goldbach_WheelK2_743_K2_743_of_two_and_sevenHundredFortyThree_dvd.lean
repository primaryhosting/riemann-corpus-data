/-
  Brockian/GoldbachWheelK2_743.lean — exact local product K₂·K_743.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_743 from def: 1 ± 1/(p−1)^{3 or 4} with p=743 → (p−1)=742.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_743

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 743) := ⟨by decide⟩

theorem Kp_sevenHundredFortyThree_of_dvd {h : ℤ} (hh : (743 : ℤ) ∣ h) :
    Kp 743 h = (408518489 / 408518488 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredFortyThree_of_not_dvd {h : ℤ} (hh : ¬(743 : ℤ) ∣ h) :
    Kp 743 h = (303120718095 / 303120718096 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredFortyThree (h : ℤ) :
    Kp 743 h = if (743 : ℤ) ∣ h then (408518489 / 408518488 : ℚ) else (303120718095 / 303120718096 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredFortyThree_of_dvd hh
  · exact Kp_sevenHundredFortyThree_of_not_dvd hh

def K2_743 (h : ℤ) : ℚ := Kp 2 h * Kp 743 h

theorem K2_743_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_743 h = 0 := by
  simp [K2_743, Kp_two_of_not_dvd h2]

theorem K2_743_of_two_and_sevenHundredFortyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (743 : ℤ) ∣ h) :
    K2_743 h = (2 : ℚ) * (408518489 / 408518488) := by
  simp [K2_743, Kp_two_of_dvd h2, Kp_sevenHundredFortyThree_of_dvd hp]

theorem K2_743_eq (h : ℤ) :
    K2_743 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (743 : ℤ) ∣ h then (408518489 / 408518488 : ℚ) else (303120718095 / 303120718096 : ℚ)) := by
  simp [K2_743, Kp_two h, Kp_sevenHundredFortyThree h]

end Brockian.Goldbach.WheelK2_743
