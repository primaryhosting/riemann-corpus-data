/-
  Brockian/GoldbachWheelK2_23.lean — exact local product K₂·K_23.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_23 from def: 1 ± 1/(p−1)^{3 or 4} with p=23 → (p−1)=22.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_23

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- If `23 ∣ h`, K_23 = 1 + 1/22³ = 10649/10648. -/
theorem Kp_twentyThree_of_dvd {h : ℤ} (hh : (23 : ℤ) ∣ h) :
    Kp 23 h = (10649 / 10648 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `23 ∤ h`, K_23 = 1 − 1/22⁴ = 234255/234256. -/
theorem Kp_twentyThree_of_not_dvd {h : ℤ} (hh : ¬(23 : ℤ) ∣ h) :
    Kp 23 h = (234255 / 234256 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_twentyThree (h : ℤ) :
    Kp 23 h = if (23 : ℤ) ∣ h then (10649 / 10648 : ℚ) else (234255 / 234256 : ℚ) := by
  split_ifs with hh
  · exact Kp_twentyThree_of_dvd hh
  · exact Kp_twentyThree_of_not_dvd hh

def K2_23 (h : ℤ) : ℚ := Kp 2 h * Kp 23 h

theorem K2_23_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_23 h = 0 := by
  simp [K2_23, Kp_two_of_not_dvd h2]

theorem K2_23_of_two_and_twentyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (23 : ℤ) ∣ h) :
    K2_23 h = (2 : ℚ) * (10649 / 10648) := by
  simp [K2_23, Kp_two_of_dvd h2, Kp_twentyThree_of_dvd hp]

theorem K2_23_eq (h : ℤ) :
    K2_23 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (23 : ℤ) ∣ h then (10649 / 10648 : ℚ) else (234255 / 234256 : ℚ)) := by
  simp [K2_23, Kp_two h, Kp_twentyThree h]

end Brockian.Goldbach.WheelK2_23
