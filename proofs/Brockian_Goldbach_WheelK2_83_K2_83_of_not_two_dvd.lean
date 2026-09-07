/-
  Brockian/GoldbachWheelK2_83.lean — exact local product K₂·K_83.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_83 from def: 1 ± 1/(p−1)^{3 or 4} with p=83 → (p−1)=82.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK2_83

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 83) := ⟨by decide⟩

theorem Kp_eightyThree_of_dvd {h : ℤ} (hh : (83 : ℤ) ∣ h) :
    Kp 83 h = (551369 / 551368 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_eightyThree_of_not_dvd {h : ℤ} (hh : ¬(83 : ℤ) ∣ h) :
    Kp 83 h = (45212175 / 45212176 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_eightyThree (h : ℤ) :
    Kp 83 h = if (83 : ℤ) ∣ h then (551369 / 551368 : ℚ) else (45212175 / 45212176 : ℚ) := by
  split_ifs with hh
  · exact Kp_eightyThree_of_dvd hh
  · exact Kp_eightyThree_of_not_dvd hh

def K2_83 (h : ℤ) : ℚ := Kp 2 h * Kp 83 h

theorem K2_83_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_83 h = 0 := by
  simp [K2_83, Kp_two_of_not_dvd h2]

theorem K2_83_of_two_and_eightyThree_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (83 : ℤ) ∣ h) :
    K2_83 h = (2 : ℚ) * (551369 / 551368) := by
  simp [K2_83, Kp_two_of_dvd h2, Kp_eightyThree_of_dvd hp]

theorem K2_83_eq (h : ℤ) :
    K2_83 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (83 : ℤ) ∣ h then (551369 / 551368 : ℚ) else (45212175 / 45212176 : ℚ)) := by
  simp [K2_83, Kp_two h, Kp_eightyThree h]

end Brockian.Goldbach.WheelK2_83
