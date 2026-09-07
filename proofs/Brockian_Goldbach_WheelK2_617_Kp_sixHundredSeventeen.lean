/-
  Brockian/GoldbachWheelK2_617.lean — exact local product K₂·K_617.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_617 from def: 1 ± 1/(p−1)^{3 or 4} with p=617 → (p−1)=616.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_617

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 617) := ⟨by decide⟩

theorem Kp_sixHundredSeventeen_of_dvd {h : ℤ} (hh : (617 : ℤ) ∣ h) :
    Kp 617 h = (233744897 / 233744896 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeventeen_of_not_dvd {h : ℤ} (hh : ¬(617 : ℤ) ∣ h) :
    Kp 617 h = (143986855935 / 143986855936 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredSeventeen (h : ℤ) :
    Kp 617 h = if (617 : ℤ) ∣ h then (233744897 / 233744896 : ℚ) else (143986855935 / 143986855936 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredSeventeen_of_dvd hh
  · exact Kp_sixHundredSeventeen_of_not_dvd hh

def K2_617 (h : ℤ) : ℚ := Kp 2 h * Kp 617 h

theorem K2_617_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_617 h = 0 := by
  simp [K2_617, Kp_two_of_not_dvd h2]

theorem K2_617_of_two_and_sixHundredSeventeen_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (617 : ℤ) ∣ h) :
    K2_617 h = (2 : ℚ) * (233744897 / 233744896) := by
  simp [K2_617, Kp_two_of_dvd h2, Kp_sixHundredSeventeen_of_dvd hp]

theorem K2_617_eq (h : ℤ) :
    K2_617 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (617 : ℤ) ∣ h then (233744897 / 233744896 : ℚ) else (143986855935 / 143986855936 : ℚ)) := by
  simp [K2_617, Kp_two h, Kp_sixHundredSeventeen h]

end Brockian.Goldbach.WheelK2_617
