/-
  Brockian/GoldbachWheelK2_199.lean — exact local product K₂·K_199.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_199 from def: 1 ± 1/(p−1)^{3 or 4} with p=199 → (p−1)=198.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_199

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 199) := ⟨by decide⟩

theorem Kp_oneHundredNinetyNine_of_dvd {h : ℤ} (hh : (199 : ℤ) ∣ h) :
    Kp 199 h = (7762393 / 7762392 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetyNine_of_not_dvd {h : ℤ} (hh : ¬(199 : ℤ) ∣ h) :
    Kp 199 h = (1536953615 / 1536953616 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_oneHundredNinetyNine (h : ℤ) :
    Kp 199 h = if (199 : ℤ) ∣ h then (7762393 / 7762392 : ℚ) else (1536953615 / 1536953616 : ℚ) := by
  split_ifs with hh
  · exact Kp_oneHundredNinetyNine_of_dvd hh
  · exact Kp_oneHundredNinetyNine_of_not_dvd hh

def K2_199 (h : ℤ) : ℚ := Kp 2 h * Kp 199 h

theorem K2_199_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_199 h = 0 := by
  simp [K2_199, Kp_two_of_not_dvd h2]

theorem K2_199_of_two_and_oneHundredNinetyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (199 : ℤ) ∣ h) :
    K2_199 h = (2 : ℚ) * (7762393 / 7762392) := by
  simp [K2_199, Kp_two_of_dvd h2, Kp_oneHundredNinetyNine_of_dvd hp]

theorem K2_199_eq (h : ℤ) :
    K2_199 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (199 : ℤ) ∣ h then (7762393 / 7762392 : ℚ) else (1536953615 / 1536953616 : ℚ)) := by
  simp [K2_199, Kp_two h, Kp_oneHundredNinetyNine h]

end Brockian.Goldbach.WheelK2_199
