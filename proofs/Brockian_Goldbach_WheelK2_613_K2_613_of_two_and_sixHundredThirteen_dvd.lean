/-
  Brockian/GoldbachWheelK2_613.lean — exact local product K₂·K_613.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_613 from def: 1 ± 1/(p−1)^{3 or 4} with p=613 → (p−1)=612.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_613

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 613) := ⟨by decide⟩

theorem Kp_sixHundredThirteen_of_dvd {h : ℤ} (hh : (613 : ℤ) ∣ h) :
    Kp 613 h = (229220929 / 229220928 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredThirteen_of_not_dvd {h : ℤ} (hh : ¬(613 : ℤ) ∣ h) :
    Kp 613 h = (140283207935 / 140283207936 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredThirteen (h : ℤ) :
    Kp 613 h = if (613 : ℤ) ∣ h then (229220929 / 229220928 : ℚ) else (140283207935 / 140283207936 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredThirteen_of_dvd hh
  · exact Kp_sixHundredThirteen_of_not_dvd hh

def K2_613 (h : ℤ) : ℚ := Kp 2 h * Kp 613 h

theorem K2_613_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_613 h = 0 := by
  simp [K2_613, Kp_two_of_not_dvd h2]

theorem K2_613_of_two_and_sixHundredThirteen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (613 : ℤ) ∣ h) :
    K2_613 h = (2 : ℚ) * (229220929 / 229220928) := by
  simp [K2_613, Kp_two_of_dvd h2, Kp_sixHundredThirteen_of_dvd hp]

theorem K2_613_eq (h : ℤ) :
    K2_613 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (613 : ℤ) ∣ h then (229220929 / 229220928 : ℚ) else (140283207935 / 140283207936 : ℚ)) := by
  simp [K2_613, Kp_two h, Kp_sixHundredThirteen h]

end Brockian.Goldbach.WheelK2_613
