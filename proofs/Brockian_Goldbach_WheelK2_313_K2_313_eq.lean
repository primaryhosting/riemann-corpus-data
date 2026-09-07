/-
  Brockian/GoldbachWheelK2_313.lean — exact local product K₂·K_313.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_313 from def: 1 ± 1/(p−1)^{3 or 4} with p=313 → (p−1)=312.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_313

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 313) := ⟨by decide⟩

theorem Kp_threeHundredThirteen_of_dvd {h : ℤ} (hh : (313 : ℤ) ∣ h) :
    Kp 313 h = (30371329 / 30371328 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredThirteen_of_not_dvd {h : ℤ} (hh : ¬(313 : ℤ) ∣ h) :
    Kp 313 h = (9475854335 / 9475854336 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_threeHundredThirteen (h : ℤ) :
    Kp 313 h = if (313 : ℤ) ∣ h then (30371329 / 30371328 : ℚ) else (9475854335 / 9475854336 : ℚ) := by
  split_ifs with hh
  · exact Kp_threeHundredThirteen_of_dvd hh
  · exact Kp_threeHundredThirteen_of_not_dvd hh

def K2_313 (h : ℤ) : ℚ := Kp 2 h * Kp 313 h

theorem K2_313_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_313 h = 0 := by
  simp [K2_313, Kp_two_of_not_dvd h2]

theorem K2_313_of_two_and_threeHundredThirteen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (313 : ℤ) ∣ h) :
    K2_313 h = (2 : ℚ) * (30371329 / 30371328) := by
  simp [K2_313, Kp_two_of_dvd h2, Kp_threeHundredThirteen_of_dvd hp]

theorem K2_313_eq (h : ℤ) :
    K2_313 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (313 : ℤ) ∣ h then (30371329 / 30371328 : ℚ) else (9475854335 / 9475854336 : ℚ)) := by
  simp [K2_313, Kp_two h, Kp_threeHundredThirteen h]

end Brockian.Goldbach.WheelK2_313
