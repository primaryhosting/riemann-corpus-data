/-
  Brockian/GoldbachWheelK2_719.lean — exact local product K₂·K_719.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_719 from def: 1 ± 1/(p−1)^{3 or 4} with p=719 → (p−1)=718.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_719

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 719) := ⟨by decide⟩

theorem Kp_sevenHundredNineteen_of_dvd {h : ℤ} (hh : (719 : ℤ) ∣ h) :
    Kp 719 h = (370146233 / 370146232 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredNineteen_of_not_dvd {h : ℤ} (hh : ¬(719 : ℤ) ∣ h) :
    Kp 719 h = (265764994575 / 265764994576 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sevenHundredNineteen (h : ℤ) :
    Kp 719 h = if (719 : ℤ) ∣ h then (370146233 / 370146232 : ℚ) else (265764994575 / 265764994576 : ℚ) := by
  split_ifs with hh
  · exact Kp_sevenHundredNineteen_of_dvd hh
  · exact Kp_sevenHundredNineteen_of_not_dvd hh

def K2_719 (h : ℤ) : ℚ := Kp 2 h * Kp 719 h

theorem K2_719_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_719 h = 0 := by
  simp [K2_719, Kp_two_of_not_dvd h2]

theorem K2_719_of_two_and_sevenHundredNineteen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (719 : ℤ) ∣ h) :
    K2_719 h = (2 : ℚ) * (370146233 / 370146232) := by
  simp [K2_719, Kp_two_of_dvd h2, Kp_sevenHundredNineteen_of_dvd hp]

theorem K2_719_eq (h : ℤ) :
    K2_719 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (719 : ℤ) ∣ h then (370146233 / 370146232 : ℚ) else (265764994575 / 265764994576 : ℚ)) := by
  simp [K2_719, Kp_two h, Kp_sevenHundredNineteen h]

end Brockian.Goldbach.WheelK2_719
