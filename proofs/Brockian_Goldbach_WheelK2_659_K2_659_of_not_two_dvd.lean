/-
  Brockian/GoldbachWheelK2_659.lean — exact local product K₂·K_659.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_659 from def: 1 ± 1/(p−1)^{3 or 4} with p=659 → (p−1)=658.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_659

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 659) := ⟨by decide⟩

theorem Kp_sixHundredFiftyNine_of_dvd {h : ℤ} (hh : (659 : ℤ) ∣ h) :
    Kp 659 h = (284890313 / 284890312 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFiftyNine_of_not_dvd {h : ℤ} (hh : ¬(659 : ℤ) ∣ h) :
    Kp 659 h = (187457825295 / 187457825296 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFiftyNine (h : ℤ) :
    Kp 659 h = if (659 : ℤ) ∣ h then (284890313 / 284890312 : ℚ) else (187457825295 / 187457825296 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredFiftyNine_of_dvd hh
  · exact Kp_sixHundredFiftyNine_of_not_dvd hh

def K2_659 (h : ℤ) : ℚ := Kp 2 h * Kp 659 h

theorem K2_659_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_659 h = 0 := by
  simp [K2_659, Kp_two_of_not_dvd h2]

theorem K2_659_of_two_and_sixHundredFiftyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (659 : ℤ) ∣ h) :
    K2_659 h = (2 : ℚ) * (284890313 / 284890312) := by
  simp [K2_659, Kp_two_of_dvd h2, Kp_sixHundredFiftyNine_of_dvd hp]

theorem K2_659_eq (h : ℤ) :
    K2_659 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (659 : ℤ) ∣ h then (284890313 / 284890312 : ℚ) else (187457825295 / 187457825296 : ℚ)) := by
  simp [K2_659, Kp_two h, Kp_sixHundredFiftyNine h]

end Brockian.Goldbach.WheelK2_659
