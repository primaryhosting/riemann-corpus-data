/-
  Brockian/GoldbachWheelK2_103.lean — exact local product K₂·K_103.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_103 from def: 1 ± 1/(p−1)^{3 or 4} with p=103 → (p−1)=102.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_103

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 103) := ⟨by decide⟩

theorem Kp_oneHundredThree_of_dvd {h : ℤ} (hh : (103 : ℤ) ∣ h) :
    Kp 103 h = (1061209 / 1061208 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThree_of_not_dvd {h : ℤ} (hh : ¬(103 : ℤ) ∣ h) :
    Kp 103 h = (108243215 / 108243216 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredThree (h : ℤ) :
    Kp 103 h = if (103 : ℤ) ∣ h then (1061209 / 1061208 : ℚ) else (108243215 / 108243216 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredThree_of_dvd hh
  · exact Kp_oneHundredThree_of_not_dvd hh

def K2_103 (h : ℤ) : ℚ := Kp 2 h * Kp 103 h

theorem K2_103_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_103 h = 0 := by
  simp [K2_103, Kp_two_of_not_dvd h2]

theorem K2_103_of_two_and_oneHundredThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (103 : ℤ) ∣ h) :
    K2_103 h = (2 : ℚ) * (1061209 / 1061208) := by
  simp [K2_103, Kp_two_of_dvd h2, Kp_oneHundredThree_of_dvd hp]

theorem K2_103_eq (h : ℤ) :
    K2_103 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (103 : ℤ) ∣ h then (1061209 / 1061208 : ℚ) else (108243215 / 108243216 : ℚ)) := by
  simp [K2_103, Kp_two h, Kp_oneHundredThree h]

end Brockian.Goldbach.WheelK2_103
