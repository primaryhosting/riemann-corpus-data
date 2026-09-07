/-
  Brockian/GoldbachWheelK2_193.lean — exact local product K₂·K_193.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_193 from def: 1 ± 1/(p−1)^{3 or 4} with p=193 → (p−1)=192.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_193

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 193) := ⟨by decide⟩

theorem Kp_oneHundredNinetyThree_of_dvd {h : ℤ} (hh : (193 : ℤ) ∣ h) :
    Kp 193 h = (7077889 / 7077888 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetyThree_of_not_dvd {h : ℤ} (hh : ¬(193 : ℤ) ∣ h) :
    Kp 193 h = (1358954495 / 1358954496 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetyThree (h : ℤ) :
    Kp 193 h = if (193 : ℤ) ∣ h then (7077889 / 7077888 : ℚ) else (1358954495 / 1358954496 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredNinetyThree_of_dvd hh
  · exact Kp_oneHundredNinetyThree_of_not_dvd hh

def K2_193 (h : ℤ) : ℚ := Kp 2 h * Kp 193 h

theorem K2_193_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_193 h = 0 := by
  simp [K2_193, Kp_two_of_not_dvd h2]

theorem K2_193_of_two_and_oneHundredNinetyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (193 : ℤ) ∣ h) :
    K2_193 h = (2 : ℚ) * (7077889 / 7077888) := by
  simp [K2_193, Kp_two_of_dvd h2, Kp_oneHundredNinetyThree_of_dvd hp]

theorem K2_193_eq (h : ℤ) :
    K2_193 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (193 : ℤ) ∣ h then (7077889 / 7077888 : ℚ) else (1358954495 / 1358954496 : ℚ)) := by
  simp [K2_193, Kp_two h, Kp_oneHundredNinetyThree h]

end Brockian.Goldbach.WheelK2_193
