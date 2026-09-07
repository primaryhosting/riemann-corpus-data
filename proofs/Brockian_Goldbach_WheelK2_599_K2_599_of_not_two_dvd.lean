/-
  Brockian/GoldbachWheelK2_599.lean — exact local product K₂·K_599.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_599 from def: 1 ± 1/(p−1)^{3 or 4} with p=599 → (p−1)=598.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_599

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 599) := ⟨by decide⟩

theorem Kp_fiveHundredNinetyNine_of_dvd {h : ℤ} (hh : (599 : ℤ) ∣ h) :
    Kp 599 h = (213847193 / 213847192 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredNinetyNine_of_not_dvd {h : ℤ} (hh : ¬(599 : ℤ) ∣ h) :
    Kp 599 h = (127880620815 / 127880620816 : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_fiveHundredNinetyNine (h : ℤ) :
    Kp 599 h = if (599 : ℤ) ∣ h then (213847193 / 213847192 : ℚ) else (127880620815 / 127880620816 : ℚ) := by
  split_ifs with hh
  · exact Kp_fiveHundredNinetyNine_of_dvd hh
  · exact Kp_fiveHundredNinetyNine_of_not_dvd hh

def K2_599 (h : ℤ) : ℚ := Kp 2 h * Kp 599 h

theorem K2_599_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) : K2_599 h = 0 := by
  simp [K2_599, Kp_two_of_not_dvd h2]

theorem K2_599_of_two_and_fiveHundredNinetyNine_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (hp : (599 : ℤ) ∣ h) :
    K2_599 h = (2 : ℚ) * (213847193 / 213847192) := by
  simp [K2_599, Kp_two_of_dvd h2, Kp_fiveHundredNinetyNine_of_dvd hp]

theorem K2_599_eq (h : ℤ) :
    K2_599 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (599 : ℤ) ∣ h then (213847193 / 213847192 : ℚ) else (127880620815 / 127880620816 : ℚ)) := by
  simp [K2_599, Kp_two h, Kp_fiveHundredNinetyNine h]

end Brockian.Goldbach.WheelK2_599
