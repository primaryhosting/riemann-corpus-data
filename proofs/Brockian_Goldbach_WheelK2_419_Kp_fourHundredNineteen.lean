/-
  Brockian/GoldbachWheelK2_419.lean — exact local product K₂·K_419.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_419 from def: 1 ± 1/(p−1)^{3 or 4} with p=419 → (p−1)=418.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_419

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 419) := ⟨by decide⟩

theorem Kp_fourHundredNineteen_of_dvd {h : ℤ} (hh : (419 : ℤ) ∣ h) :
    Kp 419 h = (73034633 / 73034632 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNineteen_of_not_dvd {h : ℤ} (hh : ¬(419 : ℤ) ∣ h) :
    Kp 419 h = (30528476175 / 30528476176 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fourHundredNineteen (h : ℤ) :
    Kp 419 h = if (419 : ℤ) ∣ h then (73034633 / 73034632 : ℚ) else (30528476175 / 30528476176 : ℚ) := by
  split_ifs with hh
  · exact Kp_fourHundredNineteen_of_dvd hh
  · exact Kp_fourHundredNineteen_of_not_dvd hh

def K2_419 (h : ℤ) : ℚ := Kp 2 h * Kp 419 h

theorem K2_419_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_419 h = 0 := by
  simp [K2_419, Kp_two_of_not_dvd h2]

theorem K2_419_of_two_and_fourHundredNineteen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (419 : ℤ) ∣ h) :
    K2_419 h = (2 : ℚ) * (73034633 / 73034632) := by
  simp [K2_419, Kp_two_of_dvd h2, Kp_fourHundredNineteen_of_dvd hp]

theorem K2_419_eq (h : ℤ) :
    K2_419 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (419 : ℤ) ∣ h then (73034633 / 73034632 : ℚ) else (30528476175 / 30528476176 : ℚ)) := by
  simp [K2_419, Kp_two h, Kp_fourHundredNineteen h]

end Brockian.Goldbach.WheelK2_419
