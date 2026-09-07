/-
  Brockian/GoldbachWheelK2_191.lean — exact local product K₂·K_191.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_191 from def: 1 ± 1/(p−1)^{3 or 4} with p=191 → (p−1)=190.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_191

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 191) := ⟨by decide⟩

theorem Kp_oneHundredNinetyOne_of_dvd {h : ℤ} (hh : (191 : ℤ) ∣ h) :
    Kp 191 h = (6859001 / 6859000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetyOne_of_not_dvd {h : ℤ} (hh : ¬(191 : ℤ) ∣ h) :
    Kp 191 h = (1303209999 / 1303210000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetyOne (h : ℤ) :
    Kp 191 h = if (191 : ℤ) ∣ h then (6859001 / 6859000 : ℚ) else (1303209999 / 1303210000 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredNinetyOne_of_dvd hh
  · exact Kp_oneHundredNinetyOne_of_not_dvd hh

def K2_191 (h : ℤ) : ℚ := Kp 2 h * Kp 191 h

theorem K2_191_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_191 h = 0 := by
  simp [K2_191, Kp_two_of_not_dvd h2]

theorem K2_191_of_two_and_oneHundredNinetyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (191 : ℤ) ∣ h) :
    K2_191 h = (2 : ℚ) * (6859001 / 6859000) := by
  simp [K2_191, Kp_two_of_dvd h2, Kp_oneHundredNinetyOne_of_dvd hp]

theorem K2_191_eq (h : ℤ) :
    K2_191 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (191 : ℤ) ∣ h then (6859001 / 6859000 : ℚ) else (1303209999 / 1303210000 : ℚ)) := by
  simp [K2_191, Kp_two h, Kp_oneHundredNinetyOne h]

end Brockian.Goldbach.WheelK2_191
