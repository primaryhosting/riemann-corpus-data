/-
  Brockian/GoldbachWheelK2_593.lean — exact local product K₂·K_593.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_593 from def: 1 ± 1/(p−1)^{3 or 4} with p=593 → (p−1)=592.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_593

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 593) := ⟨by decide⟩

theorem Kp_fiveHundredNinetyThree_of_dvd {h : ℤ} (hh : (593 : ℤ) ∣ h) :
    Kp 593 h = (207474689 / 207474688 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredNinetyThree_of_not_dvd {h : ℤ} (hh : ¬(593 : ℤ) ∣ h) :
    Kp 593 h = (122825015295 / 122825015296 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredNinetyThree (h : ℤ) :
    Kp 593 h = if (593 : ℤ) ∣ h then (207474689 / 207474688 : ℚ) else (122825015295 / 122825015296 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredNinetyThree_of_dvd hh
  · exact Kp_fiveHundredNinetyThree_of_not_dvd hh

def K2_593 (h : ℤ) : ℚ := Kp 2 h * Kp 593 h

theorem K2_593_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_593 h = 0 := by
  simp [K2_593, Kp_two_of_not_dvd h2]

theorem K2_593_of_two_and_fiveHundredNinetyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (593 : ℤ) ∣ h) :
    K2_593 h = (2 : ℚ) * (207474689 / 207474688) := by
  simp [K2_593, Kp_two_of_dvd h2, Kp_fiveHundredNinetyThree_of_dvd hp]

theorem K2_593_eq (h : ℤ) :
    K2_593 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (593 : ℤ) ∣ h then (207474689 / 207474688 : ℚ) else (122825015295 / 122825015296 : ℚ)) := by
  simp [K2_593, Kp_two h, Kp_fiveHundredNinetyThree h]

end Brockian.Goldbach.WheelK2_593
