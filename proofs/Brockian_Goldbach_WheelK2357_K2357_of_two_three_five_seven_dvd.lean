/-
  Brockian/GoldbachWheelK2357.lean — four-prime finite local Goldbach wheel
  K₂K₃K₅K₇.

  HONEST SCOPE: this module does NOT prove the Goldbach conjecture, does not
  assert a global representation theorem for even integers, and does not claim
  the empirical/asymptotic Goldbach residual transfer.  It extends
  GoldbachLocalWheel / GoldbachWheelExtended with the exact four-prime product
  wheel K2357 = K₂ · K₃ · K₅ · K₇ and a full case table by divisibility by
  2, 3, 5, 7.

  Contents (PROVED, unconditional, axiom-clean over Mathlib):
    * def `K2357` and relation to `K235` / individual `Kp`
    * full case table by (2|h, 3|h, 5|h, 7|h)
    * nonnegativity, upper bound = fully aligned value `14105/6144`
    * positivity exactly on even shifts (zero iff odd)
    * characterization of full 2–3–5–7 alignment

  Imports: GoldbachComb, GoldbachLocalWheel, GoldbachWheelExtended,
  GoldbachParity, GoldbachLemmas only.

  Verification: AXLE `check` @ lean-4.32.0; #print axioms ⊆
  {propext, Classical.choice, Quot.sound}. No sorry / admit / axiom /
  native_decide.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachLocalWheel
import Brockian.GoldbachWheelExtended
import Brockian.GoldbachParity
import Brockian.GoldbachLemmas

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Brockian.Goldbach.WheelK2357

open Finset
open Brockian.GoldbachComb
open Brockian.Goldbach.LocalWheel
open Brockian.Goldbach.WheelExtended
open Brockian.Goldbach.Parity
open Brockian.GoldbachLemmas

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ## The finite p = 2,3,5,7 covariance wheel -/

/-- The finite covariance product over the four local primes 2, 3, 5, 7.
Exact finite arithmetic; not a transfer claim. -/
def K2357 (h : ℤ) : ℚ :=
  Kp 2 h * Kp 3 h * Kp 5 h * Kp 7 h

/-- Relates the four-prime wheel to the three-prime wheel of `WheelExtended`. -/
theorem K2357_eq_K235_mul_Kp_seven (h : ℤ) : K2357 h = K235 h * Kp 7 h := by
  simp [K2357, K235, mul_assoc]

/-- Relates the four-prime wheel to the two-prime wheel times the odd factors. -/
theorem K2357_eq_K23_mul_Kp_five_mul_Kp_seven (h : ℤ) :
    K2357 h = K23 h * Kp 5 h * Kp 7 h := by
  simp [K2357, K23, mul_assoc]

/-! ## Case values by divisibility pattern -/

/-- Odd shifts are killed by the p = 2 factor. -/
theorem K2357_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) :
    K2357 h = 0 := by
  simp [K2357, Kp_two_of_not_dvd h2]

/-- Fully aligned: even and 3-, 5-, 7-divisible → `14105/6144`. -/
theorem K2357_of_two_three_five_seven_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : (3 : ℤ) ∣ h) (h5 : (5 : ℤ) ∣ h) (h7 : (7 : ℤ) ∣ h) :
    K2357 h = (14105 / 6144 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_dvd h3, Kp_five_of_dvd h5,
    Kp_seven_of_dvd h7]
  norm_num

/-- Even, 3-, 5-divisible, not 7: `84175/36864`. -/
theorem K2357_of_two_three_five_dvd_not_seven {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : (3 : ℤ) ∣ h) (h5 : (5 : ℤ) ∣ h) (h7 : ¬(7 : ℤ) ∣ h) :
    K2357 h = (84175 / 36864 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_dvd h3, Kp_five_of_dvd h5,
    Kp_seven_of_not_dvd h7]
  norm_num

/-- Even, 3-, 7-divisible, not 5: `18445/8192`. -/
theorem K2357_of_two_three_seven_dvd_not_five {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : (3 : ℤ) ∣ h) (h5 : ¬(5 : ℤ) ∣ h) (h7 : (7 : ℤ) ∣ h) :
    K2357 h = (18445 / 8192 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_dvd h3, Kp_five_of_not_dvd h5,
    Kp_seven_of_dvd h7]
  norm_num

/-- Even, 3-divisible, neither 5 nor 7: `110075/49152`. -/
theorem K2357_of_two_three_dvd_not_five_not_seven {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : (3 : ℤ) ∣ h) (h5 : ¬(5 : ℤ) ∣ h) (h7 : ¬(7 : ℤ) ∣ h) :
    K2357 h = (110075 / 49152 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_dvd h3, Kp_five_of_not_dvd h5,
    Kp_seven_of_not_dvd h7]
  norm_num

/-- Even, 5-, 7-divisible, not 3: `70525/36864`. -/
theorem K2357_of_two_five_seven_dvd_not_three {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : ¬(3 : ℤ) ∣ h) (h5 : (5 : ℤ) ∣ h) (h7 : (7 : ℤ) ∣ h) :
    K2357 h = (70525 / 36864 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_not_dvd h3, Kp_five_of_dvd h5,
    Kp_seven_of_dvd h7]
  norm_num

/-- Even, 5-divisible, neither 3 nor 7: `420875/221184`. -/
theorem K2357_of_two_five_dvd_not_three_not_seven {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : ¬(3 : ℤ) ∣ h) (h5 : (5 : ℤ) ∣ h) (h7 : ¬(7 : ℤ) ∣ h) :
    K2357 h = (420875 / 221184 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_not_dvd h3, Kp_five_of_dvd h5,
    Kp_seven_of_not_dvd h7]
  norm_num

/-- Even, 7-divisible, neither 3 nor 5: `92225/49152`. -/
theorem K2357_of_two_seven_dvd_not_three_not_five {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : ¬(3 : ℤ) ∣ h) (h5 : ¬(5 : ℤ) ∣ h) (h7 : (7 : ℤ) ∣ h) :
    K2357 h = (92225 / 49152 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_not_dvd h3, Kp_five_of_not_dvd h5,
    Kp_seven_of_dvd h7]
  norm_num

/-- Even, none of 3, 5, 7: baseline `550375/294912`. -/
theorem K2357_of_two_dvd_not_three_not_five_not_seven {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : ¬(3 : ℤ) ∣ h) (h5 : ¬(5 : ℤ) ∣ h) (h7 : ¬(7 : ℤ) ∣ h) :
    K2357 h = (550375 / 294912 : ℚ) := by
  simp [K2357, Kp_two_of_dvd h2, Kp_three_of_not_dvd h3, Kp_five_of_not_dvd h5,
    Kp_seven_of_not_dvd h7]
  norm_num

/-- Closed form of the 2–3–5–7 wheel via closed forms of `K₂`, `K₃`, `K₅`, `K₇`. -/
theorem K2357_eq (h : ℤ) :
    K2357 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (3 : ℤ) ∣ h then (9 / 8 : ℚ) else (15 / 16 : ℚ)) *
      (if (5 : ℤ) ∣ h then (65 / 64 : ℚ) else (255 / 256 : ℚ)) *
      (if (7 : ℤ) ∣ h then (217 / 216 : ℚ) else (1295 / 1296 : ℚ)) := by
  simp [K2357, Kp_two h, Kp_three h, Kp_five h, Kp_seven h]

/-- Case table: every divisibility pattern for the four-prime wheel. -/
theorem K2357_cases (h : ℤ) :
    K2357 h =
      if ¬(2 : ℤ) ∣ h then (0 : ℚ)
      else if (3 : ℤ) ∣ h then
        if (5 : ℤ) ∣ h then
          if (7 : ℤ) ∣ h then (14105 / 6144 : ℚ) else (84175 / 36864 : ℚ)
        else if (7 : ℤ) ∣ h then (18445 / 8192 : ℚ)
        else (110075 / 49152 : ℚ)
      else if (5 : ℤ) ∣ h then
        if (7 : ℤ) ∣ h then (70525 / 36864 : ℚ) else (420875 / 221184 : ℚ)
      else if (7 : ℤ) ∣ h then (92225 / 49152 : ℚ)
      else (550375 / 294912 : ℚ) := by
  by_cases h2 : (2 : ℤ) ∣ h
  · by_cases h3 : (3 : ℤ) ∣ h
    · by_cases h5 : (5 : ℤ) ∣ h
      · by_cases h7 : (7 : ℤ) ∣ h
        · simp [h2, h3, h5, h7, K2357_of_two_three_five_seven_dvd h2 h3 h5 h7]
        · simp [h2, h3, h5, h7, K2357_of_two_three_five_dvd_not_seven h2 h3 h5 h7]
      · by_cases h7 : (7 : ℤ) ∣ h
        · simp [h2, h3, h5, h7, K2357_of_two_three_seven_dvd_not_five h2 h3 h5 h7]
        · simp [h2, h3, h5, h7, K2357_of_two_three_dvd_not_five_not_seven h2 h3 h5 h7]
    · by_cases h5 : (5 : ℤ) ∣ h
      · by_cases h7 : (7 : ℤ) ∣ h
        · simp [h2, h3, h5, h7, K2357_of_two_five_seven_dvd_not_three h2 h3 h5 h7]
        · simp [h2, h3, h5, h7, K2357_of_two_five_dvd_not_three_not_seven h2 h3 h5 h7]
      · by_cases h7 : (7 : ℤ) ∣ h
        · simp [h2, h3, h5, h7, K2357_of_two_seven_dvd_not_three_not_five h2 h3 h5 h7]
        · simp [h2, h3, h5, h7, K2357_of_two_dvd_not_three_not_five_not_seven h2 h3 h5 h7]
  · simp [h2, K2357_of_not_two_dvd h2]

/-! ## Nonnegativity, upper bound, zero iff odd, aligned max -/

/-- The p = 2,3,5,7 product is nonnegative for every shift. -/
theorem K2357_nonneg (h : ℤ) : 0 ≤ K2357 h := by
  rw [K2357_eq]
  split_ifs <;> norm_num

/-- The p = 2,3,5,7 product never exceeds the fully aligned value `14105/6144`. -/
theorem K2357_le_aligned (h : ℤ) : K2357 h ≤ (14105 / 6144 : ℚ) := by
  rw [K2357_eq]
  split_ifs <;> norm_num

/-- The p = 2,3,5,7 product is zero exactly on odd shifts. -/
theorem K2357_eq_zero_iff_not_two_dvd (h : ℤ) :
    K2357 h = 0 ↔ ¬(2 : ℤ) ∣ h := by
  constructor
  · intro hz
    by_contra h2
    have h2' : (2 : ℤ) ∣ h := by simpa using h2
    by_cases h3 : (3 : ℤ) ∣ h
    · by_cases h5 : (5 : ℤ) ∣ h
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_three_five_seven_dvd h2' h3 h5 h7] at hz; norm_num at hz
        · rw [K2357_of_two_three_five_dvd_not_seven h2' h3 h5 h7] at hz; norm_num at hz
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_three_seven_dvd_not_five h2' h3 h5 h7] at hz; norm_num at hz
        · rw [K2357_of_two_three_dvd_not_five_not_seven h2' h3 h5 h7] at hz; norm_num at hz
    · by_cases h5 : (5 : ℤ) ∣ h
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_five_seven_dvd_not_three h2' h3 h5 h7] at hz; norm_num at hz
        · rw [K2357_of_two_five_dvd_not_three_not_seven h2' h3 h5 h7] at hz; norm_num at hz
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_seven_dvd_not_three_not_five h2' h3 h5 h7] at hz; norm_num at hz
        · rw [K2357_of_two_dvd_not_three_not_five_not_seven h2' h3 h5 h7] at hz; norm_num at hz
  · intro h2
    exact K2357_of_not_two_dvd h2

/-- The p = 2,3,5,7 product is positive exactly on even shifts. -/
theorem K2357_pos_iff_two_dvd (h : ℤ) :
    0 < K2357 h ↔ (2 : ℤ) ∣ h := by
  constructor
  · intro hpos
    by_contra h2
    rw [K2357_of_not_two_dvd h2] at hpos
    exact (lt_irrefl (0 : ℚ) hpos)
  · intro h2
    by_cases h3 : (3 : ℤ) ∣ h
    · by_cases h5 : (5 : ℤ) ∣ h
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_three_five_seven_dvd h2 h3 h5 h7]; norm_num
        · rw [K2357_of_two_three_five_dvd_not_seven h2 h3 h5 h7]; norm_num
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_three_seven_dvd_not_five h2 h3 h5 h7]; norm_num
        · rw [K2357_of_two_three_dvd_not_five_not_seven h2 h3 h5 h7]; norm_num
    · by_cases h5 : (5 : ℤ) ∣ h
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_five_seven_dvd_not_three h2 h3 h5 h7]; norm_num
        · rw [K2357_of_two_five_dvd_not_three_not_seven h2 h3 h5 h7]; norm_num
      · by_cases h7 : (7 : ℤ) ∣ h
        · rw [K2357_of_two_seven_dvd_not_three_not_five h2 h3 h5 h7]; norm_num
        · rw [K2357_of_two_dvd_not_three_not_five_not_seven h2 h3 h5 h7]; norm_num

/-- Equality with the fully aligned value characterises simultaneous 2-, 3-, 5-,
and 7-divisibility. -/
theorem K2357_eq_aligned_iff (h : ℤ) :
    K2357 h = (14105 / 6144 : ℚ) ↔
      (2 : ℤ) ∣ h ∧ (3 : ℤ) ∣ h ∧ (5 : ℤ) ∣ h ∧ (7 : ℤ) ∣ h := by
  constructor
  · intro heq
    by_cases h2 : (2 : ℤ) ∣ h
    · by_cases h3 : (3 : ℤ) ∣ h
      · by_cases h5 : (5 : ℤ) ∣ h
        · by_cases h7 : (7 : ℤ) ∣ h
          · exact ⟨h2, h3, h5, h7⟩
          · rw [K2357_of_two_three_five_dvd_not_seven h2 h3 h5 h7] at heq
            norm_num at heq
        · by_cases h7 : (7 : ℤ) ∣ h
          · rw [K2357_of_two_three_seven_dvd_not_five h2 h3 h5 h7] at heq
            norm_num at heq
          · rw [K2357_of_two_three_dvd_not_five_not_seven h2 h3 h5 h7] at heq
            norm_num at heq
      · by_cases h5 : (5 : ℤ) ∣ h
        · by_cases h7 : (7 : ℤ) ∣ h
          · rw [K2357_of_two_five_seven_dvd_not_three h2 h3 h5 h7] at heq
            norm_num at heq
          · rw [K2357_of_two_five_dvd_not_three_not_seven h2 h3 h5 h7] at heq
            norm_num at heq
        · by_cases h7 : (7 : ℤ) ∣ h
          · rw [K2357_of_two_seven_dvd_not_three_not_five h2 h3 h5 h7] at heq
            norm_num at heq
          · rw [K2357_of_two_dvd_not_three_not_five_not_seven h2 h3 h5 h7] at heq
            norm_num at heq
    · rw [K2357_of_not_two_dvd h2] at heq
      norm_num at heq
  · rintro ⟨h2, h3, h5, h7⟩
    exact K2357_of_two_three_five_seven_dvd h2 h3 h5 h7

/-- On even shifts the finite excess over the even baseline is nonnegative. -/
theorem K2357_excess_nonneg_of_even {h : ℤ} (h2 : (2 : ℤ) ∣ h) :
    0 ≤ K2357 h - (550375 / 294912 : ℚ) := by
  by_cases h3 : (3 : ℤ) ∣ h
  · by_cases h5 : (5 : ℤ) ∣ h
    · by_cases h7 : (7 : ℤ) ∣ h
      · rw [K2357_of_two_three_five_seven_dvd h2 h3 h5 h7]; norm_num
      · rw [K2357_of_two_three_five_dvd_not_seven h2 h3 h5 h7]; norm_num
    · by_cases h7 : (7 : ℤ) ∣ h
      · rw [K2357_of_two_three_seven_dvd_not_five h2 h3 h5 h7]; norm_num
      · rw [K2357_of_two_three_dvd_not_five_not_seven h2 h3 h5 h7]; norm_num
  · by_cases h5 : (5 : ℤ) ∣ h
    · by_cases h7 : (7 : ℤ) ∣ h
      · rw [K2357_of_two_five_seven_dvd_not_three h2 h3 h5 h7]; norm_num
      · rw [K2357_of_two_five_dvd_not_three_not_seven h2 h3 h5 h7]; norm_num
    · by_cases h7 : (7 : ℤ) ∣ h
      · rw [K2357_of_two_seven_dvd_not_three_not_five h2 h3 h5 h7]; norm_num
      · rw [K2357_of_two_dvd_not_three_not_five_not_seven h2 h3 h5 h7]; norm_num

/-- Fully aligned four-prime wheel value strictly exceeds the even baseline. -/
theorem K2357_aligned_gt_baseline : (550375 / 294912 : ℚ) < (14105 / 6144 : ℚ) := by
  norm_num

/-- Fully aligned four-prime value strictly exceeds the three-prime aligned value
`585/256` (because the aligned p = 7 factor is `217/216 > 1`). -/
theorem K2357_aligned_gt_K235_aligned : (585 / 256 : ℚ) < (14105 / 6144 : ℚ) := by
  norm_num

/-- Fully aligned four-prime value strictly exceeds the two-prime aligned value `9/4`. -/
theorem K2357_aligned_gt_K23_aligned : (9 / 4 : ℚ) < (14105 / 6144 : ℚ) := by
  norm_num

end Brockian.Goldbach.WheelK2357
