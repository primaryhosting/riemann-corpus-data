/-
  Brockian/GoldbachWheelK2_59.lean — exact local product K₂·K_59.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_59 from def: 1 ± 1/(p−1)^{3 or 4} with p=59 → (p−1)=58.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_59

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 59) := ⟨by decide⟩

theorem Kp_fiftyNine_of_dvd {h : ℤ} (hh : (59 : ℤ) ∣ h) :
    Kp 59 h = (195113 / 195112 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiftyNine_of_not_dvd {h : ℤ} (hh : ¬(59 : ℤ) ∣ h) :
    Kp 59 h = (11316495 / 11316496 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiftyNine (h : ℤ) :
    Kp 59 h = if (59 : ℤ) ∣ h then (195113 / 195112 : ℚ) else (11316495 / 11316496 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiftyNine_of_dvd hh
  · exact Kp_fiftyNine_of_not_dvd hh

def K2_59 (h : ℤ) : ℚ := Kp 2 h * Kp 59 h

theorem K2_59_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_59 h = 0 := by
  simp [K2_59, Kp_two_of_not_dvd h2]

theorem K2_59_of_two_and_fiftyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (59 : ℤ) ∣ h) :
    K2_59 h = (2 : ℚ) * (195113 / 195112) := by
  simp [K2_59, Kp_two_of_dvd h2, Kp_fiftyNine_of_dvd hp]

theorem K2_59_eq (h : ℤ) :
    K2_59 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (59 : ℤ) ∣ h then (195113 / 195112 : ℚ) else (11316495 / 11316496 : ℚ)) := by
  simp [K2_59, Kp_two h, Kp_fiftyNine h]

end Brockian.Goldbach.WheelK2_59
