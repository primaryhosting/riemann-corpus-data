/-
  Brockian/GoldbachWheelK2_677.lean — exact local product K₂·K_677.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_677 from def: 1 ± 1/(p−1)^{3 or 4} with p=677 → (p−1)=676.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_677

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 677) := ⟨by decide⟩

theorem Kp_sixHundredSeventySeven_of_dvd {h : ℤ} (hh : (677 : ℤ) ∣ h) :
    Kp 677 h = (308915777 / 308915776 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeventySeven_of_not_dvd {h : ℤ} (hh : ¬(677 : ℤ) ∣ h) :
    Kp 677 h = (208827064575 / 208827064576 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeventySeven (h : ℤ) :
    Kp 677 h = if (677 : ℤ) ∣ h then (308915777 / 308915776 : ℚ) else (208827064575 / 208827064576 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredSeventySeven_of_dvd hh
  · exact Kp_sixHundredSeventySeven_of_not_dvd hh

def K2_677 (h : ℤ) : ℚ := Kp 2 h * Kp 677 h

theorem K2_677_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_677 h = 0 := by
  simp [K2_677, Kp_two_of_not_dvd h2]

theorem K2_677_of_two_and_sixHundredSeventySeven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (677 : ℤ) ∣ h) :
    K2_677 h = (2 : ℚ) * (308915777 / 308915776) := by
  simp [K2_677, Kp_two_of_dvd h2, Kp_sixHundredSeventySeven_of_dvd hp]

theorem K2_677_eq (h : ℤ) :
    K2_677 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (677 : ℤ) ∣ h then (308915777 / 308915776 : ℚ) else (208827064575 / 208827064576 : ℚ)) := by
  simp [K2_677, Kp_two h, Kp_sixHundredSeventySeven h]

end Brockian.Goldbach.WheelK2_677
