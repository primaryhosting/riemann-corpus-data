/-
  Brockian/GoldbachWheelK2_509.lean — exact local product K₂·K_509.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_509 from def: 1 ± 1/(p−1)^{3 or 4} with p=509 → (p−1)=508.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_509

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 509) := ⟨by decide⟩

theorem Kp_fiveHundredNine_of_dvd {h : ℤ} (hh : (509 : ℤ) ∣ h) :
    Kp 509 h = (131096513 / 131096512 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredNine_of_not_dvd {h : ℤ} (hh : ¬(509 : ℤ) ∣ h) :
    Kp 509 h = (66597028095 / 66597028096 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredNine (h : ℤ) :
    Kp 509 h = if (509 : ℤ) ∣ h then (131096513 / 131096512 : ℚ) else (66597028095 / 66597028096 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredNine_of_dvd hh
  · exact Kp_fiveHundredNine_of_not_dvd hh

def K2_509 (h : ℤ) : ℚ := Kp 2 h * Kp 509 h

theorem K2_509_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_509 h = 0 := by
  simp [K2_509, Kp_two_of_not_dvd h2]

theorem K2_509_of_two_and_fiveHundredNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (509 : ℤ) ∣ h) :
    K2_509 h = (2 : ℚ) * (131096513 / 131096512) := by
  simp [K2_509, Kp_two_of_dvd h2, Kp_fiveHundredNine_of_dvd hp]

theorem K2_509_eq (h : ℤ) :
    K2_509 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (509 : ℤ) ∣ h then (131096513 / 131096512 : ℚ) else (66597028095 / 66597028096 : ℚ)) := by
  simp [K2_509, Kp_two h, Kp_fiveHundredNine h]

end Brockian.Goldbach.WheelK2_509
