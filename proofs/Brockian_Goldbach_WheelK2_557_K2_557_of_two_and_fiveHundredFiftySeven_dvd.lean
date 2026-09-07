/-
  Brockian/GoldbachWheelK2_557.lean — exact local product K₂·K_557.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_557 from def: 1 ± 1/(p−1)^{3 or 4} with p=557 → (p−1)=556.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_557

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 557) := ⟨by decide⟩

theorem Kp_fiveHundredFiftySeven_of_dvd {h : ℤ} (hh : (557 : ℤ) ∣ h) :
    Kp 557 h = (171879617 / 171879616 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredFiftySeven_of_not_dvd {h : ℤ} (hh : ¬(557 : ℤ) ∣ h) :
    Kp 557 h = (95565066495 / 95565066496 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredFiftySeven (h : ℤ) :
    Kp 557 h = if (557 : ℤ) ∣ h then (171879617 / 171879616 : ℚ) else (95565066495 / 95565066496 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredFiftySeven_of_dvd hh
  · exact Kp_fiveHundredFiftySeven_of_not_dvd hh

def K2_557 (h : ℤ) : ℚ := Kp 2 h * Kp 557 h

theorem K2_557_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_557 h = 0 := by
  simp [K2_557, Kp_two_of_not_dvd h2]

theorem K2_557_of_two_and_fiveHundredFiftySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (557 : ℤ) ∣ h) :
    K2_557 h = (2 : ℚ) * (171879617 / 171879616) := by
  simp [K2_557, Kp_two_of_dvd h2, Kp_fiveHundredFiftySeven_of_dvd hp]

theorem K2_557_eq (h : ℤ) :
    K2_557 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (557 : ℤ) ∣ h then (171879617 / 171879616 : ℚ) else (95565066495 / 95565066496 : ℚ)) := by
  simp [K2_557, Kp_two h, Kp_fiveHundredFiftySeven h]

end Brockian.Goldbach.WheelK2_557
