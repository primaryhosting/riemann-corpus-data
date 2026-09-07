/-
  K₂·K₁₁ finite product closed forms. HONEST: not Goldbach.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity
import Brockian.GoldbachWheelExtended

set_option autoImplicit false

namespace Brockian.Goldbach.WheelK235711

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity
open Brockian.Goldbach.WheelExtended

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def K2_11 (h : ℤ) : ℚ := Kp 2 h * Kp 11 h

theorem K2_11_of_not_two_dvd {h : ℤ} (h2 : ¬ (2 : ℤ) ∣ h) : K2_11 h = 0 := by
  simp [K2_11, Kp_two_of_not_dvd h2]

theorem K2_11_of_two_and_eleven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h11 : (11 : ℤ) ∣ h) :
    K2_11 h = (2 : ℚ) * (1001 / 1000) := by
  simp [K2_11, Kp_two_of_dvd h2, Kp_eleven_of_dvd h11]

theorem K2_11_eq (h : ℤ) :
    K2_11 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (11 : ℤ) ∣ h then (1001 / 1000 : ℚ) else (9999 / 10000 : ℚ)) := by
  simp [K2_11, Kp_two h, Kp_eleven h]

end Brockian.Goldbach.WheelK235711
