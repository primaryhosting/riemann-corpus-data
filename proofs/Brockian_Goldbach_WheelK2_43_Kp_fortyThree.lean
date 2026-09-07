/-
  Brockian/GoldbachWheelK2_43.lean — exact local product K₂·K_43.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_43 from def: 1 ± 1/(p−1)^{3 or 4} with p=43 → (p−1)=42.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_43

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 43) := ⟨by decide⟩

theorem Kp_fortyThree_of_dvd {h : ℤ} (hh : (43 : ℤ) ∣ h) :
    Kp 43 h = (74089 / 74088 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fortyThree_of_not_dvd {h : ℤ} (hh : ¬(43 : ℤ) ∣ h) :
    Kp 43 h = (3111695 / 3111696 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fortyThree (h : ℤ) :
    Kp 43 h = if (43 : ℤ) ∣ h then (74089 / 74088 : ℚ) else (3111695 / 3111696 : ℚ) := by
  split_ifs with hh
  · exact Kp_fortyThree_of_dvd hh
  · exact Kp_fortyThree_of_not_dvd hh

def K2_43 (h : ℤ) : ℚ := Kp 2 h * Kp 43 h

theorem K2_43_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_43 h = 0 := by
  simp [K2_43, Kp_two_of_not_dvd h2]

theorem K2_43_of_two_and_fortyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (43 : ℤ) ∣ h) :
    K2_43 h = (2 : ℚ) * (74089 / 74088) := by
  simp [K2_43, Kp_two_of_dvd h2, Kp_fortyThree_of_dvd hp]

theorem K2_43_eq (h : ℤ) :
    K2_43 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (43 : ℤ) ∣ h then (74089 / 74088 : ℚ) else (3111695 / 3111696 : ℚ)) := by
  simp [K2_43, Kp_two h, Kp_fortyThree h]

end Brockian.Goldbach.WheelK2_43
