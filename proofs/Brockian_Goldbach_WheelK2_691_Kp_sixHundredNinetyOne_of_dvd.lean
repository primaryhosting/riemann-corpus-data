/-
  Brockian/GoldbachWheelK2_691.lean — exact local product K₂·K_691.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_691 from def: 1 ± 1/(p−1)^{3 or 4} with p=691 → (p−1)=690.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_691

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 691) := ⟨by decide⟩

theorem Kp_sixHundredNinetyOne_of_dvd {h : ℤ} (hh : (691 : ℤ) ∣ h) :
    Kp 691 h = (328509001 / 328509000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredNinetyOne_of_not_dvd {h : ℤ} (hh : ¬(691 : ℤ) ∣ h) :
    Kp 691 h = (226671209999 / 226671210000 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_sixHundredNinetyOne (h : ℤ) :
    Kp 691 h = if (691 : ℤ) ∣ h then (328509001 / 328509000 : ℚ) else (226671209999 / 226671210000 : ℚ) := by
  split_ifs with hh
  · exact Kp_sixHundredNinetyOne_of_dvd hh
  · exact Kp_sixHundredNinetyOne_of_not_dvd hh

def K2_691 (h : ℤ) : ℚ := Kp 2 h * Kp 691 h

theorem K2_691_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_691 h = 0 := by
  simp [K2_691, Kp_two_of_not_dvd h2]

theorem K2_691_of_two_and_sixHundredNinetyOne_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (691 : ℤ) ∣ h) :
    K2_691 h = (2 : ℚ) * (328509001 / 328509000) := by
  simp [K2_691, Kp_two_of_dvd h2, Kp_sixHundredNinetyOne_of_dvd hp]

theorem K2_691_eq (h : ℤ) :
    K2_691 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (691 : ℤ) ∣ h then (328509001 / 328509000 : ℚ) else (226671209999 / 226671210000 : ℚ)) := by
  simp [K2_691, Kp_two h, Kp_sixHundredNinetyOne h]

end Brockian.Goldbach.WheelK2_691
