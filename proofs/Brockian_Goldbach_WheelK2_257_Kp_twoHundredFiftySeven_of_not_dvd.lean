/-
  Brockian/GoldbachWheelK2_257.lean — exact local product K₂·K_257.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_257 from def: 1 ± 1/(p−1)^{3 or 4} with p=257 → (p−1)=256.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_257

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 257) := ⟨by decide⟩

theorem Kp_twoHundredFiftySeven_of_dvd {h : ℤ} (hh : (257 : ℤ) ∣ h) :
    Kp 257 h = (16777217 / 16777216 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredFiftySeven_of_not_dvd {h : ℤ} (hh : ¬(257 : ℤ) ∣ h) :
    Kp 257 h = (4294967295 / 4294967296 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twoHundredFiftySeven (h : ℤ) :
    Kp 257 h = if (257 : ℤ) ∣ h then (16777217 / 16777216 : ℚ) else (4294967295 / 4294967296 : ℚ) := by
  split_ifs with hh
  · exact Kp_twoHundredFiftySeven_of_dvd hh
  · exact Kp_twoHundredFiftySeven_of_not_dvd hh

def K2_257 (h : ℤ) : ℚ := Kp 2 h * Kp 257 h

theorem K2_257_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_257 h = 0 := by
  simp [K2_257, Kp_two_of_not_dvd h2]

theorem K2_257_of_two_and_twoHundredFiftySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (257 : ℤ) ∣ h) :
    K2_257 h = (2 : ℚ) * (16777217 / 16777216) := by
  simp [K2_257, Kp_two_of_dvd h2, Kp_twoHundredFiftySeven_of_dvd hp]

theorem K2_257_eq (h : ℤ) :
    K2_257 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (257 : ℤ) ∣ h then (16777217 / 16777216 : ℚ) else (4294967295 / 4294967296 : ℚ)) := by
  simp [K2_257, Kp_two h, Kp_twoHundredFiftySeven h]

end Brockian.Goldbach.WheelK2_257
