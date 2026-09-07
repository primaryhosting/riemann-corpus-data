/-
  Brockian/GoldbachWheelK2_53.lean — exact local product K₂·K_53.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_53 from def: 1 ± 1/(p−1)^{3 or 4} with p=53 → (p−1)=52.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_53

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 53) := ⟨by decide⟩

theorem Kp_fiftyThree_of_dvd {h : ℤ} (hh : (53 : ℤ) ∣ h) :
    Kp 53 h = (140609 / 140608 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiftyThree_of_not_dvd {h : ℤ} (hh : ¬(53 : ℤ) ∣ h) :
    Kp 53 h = (7311615 / 7311616 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiftyThree (h : ℤ) :
    Kp 53 h = if (53 : ℤ) ∣ h then (140609 / 140608 : ℚ) else (7311615 / 7311616 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiftyThree_of_dvd hh
  · exact Kp_fiftyThree_of_not_dvd hh

def K2_53 (h : ℤ) : ℚ := Kp 2 h * Kp 53 h

theorem K2_53_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_53 h = 0 := by
  simp [K2_53, Kp_two_of_not_dvd h2]

theorem K2_53_of_two_and_fiftyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (53 : ℤ) ∣ h) :
    K2_53 h = (2 : ℚ) * (140609 / 140608) := by
  simp [K2_53, Kp_two_of_dvd h2, Kp_fiftyThree_of_dvd hp]

theorem K2_53_eq (h : ℤ) :
    K2_53 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (53 : ℤ) ∣ h then (140609 / 140608 : ℚ) else (7311615 / 7311616 : ℚ)) := by
  simp [K2_53, Kp_two h, Kp_fiftyThree h]

end Brockian.Goldbach.WheelK2_53
