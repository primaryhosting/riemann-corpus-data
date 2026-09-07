/-
  Brockian/GoldbachWheelK2_653.lean — exact local product K₂·K_653.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_653 from def: 1 ± 1/(p−1)^{3 or 4} with p=653 → (p−1)=652.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_653

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 653) := ⟨by decide⟩

theorem Kp_sixHundredFiftyThree_of_dvd {h : ℤ} (hh : (653 : ℤ) ∣ h) :
    Kp 653 h = (277167809 / 277167808 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFiftyThree_of_not_dvd {h : ℤ} (hh : ¬(653 : ℤ) ∣ h) :
    Kp 653 h = (180713410815 / 180713410816 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredFiftyThree (h : ℤ) :
    Kp 653 h = if (653 : ℤ) ∣ h then (277167809 / 277167808 : ℚ) else (180713410815 / 180713410816 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredFiftyThree_of_dvd hh
  · exact Kp_sixHundredFiftyThree_of_not_dvd hh

def K2_653 (h : ℤ) : ℚ := Kp 2 h * Kp 653 h

theorem K2_653_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_653 h = 0 := by
  simp [K2_653, Kp_two_of_not_dvd h2]

theorem K2_653_of_two_and_sixHundredFiftyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (653 : ℤ) ∣ h) :
    K2_653 h = (2 : ℚ) * (277167809 / 277167808) := by
  simp [K2_653, Kp_two_of_dvd h2, Kp_sixHundredFiftyThree_of_dvd hp]

theorem K2_653_eq (h : ℤ) :
    K2_653 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (653 : ℤ) ∣ h then (277167809 / 277167808 : ℚ) else (180713410815 / 180713410816 : ℚ)) := by
  simp [K2_653, Kp_two h, Kp_sixHundredFiftyThree h]

end Brockian.Goldbach.WheelK2_653
