/-
  Brockian/GoldbachWheelExtended.lean — extended finite local Goldbach wheels.

  HONEST SCOPE: this module does NOT prove the Goldbach conjecture, does not
  assert a global representation theorem for even integers, and does not claim
  the empirical/asymptotic Goldbach residual transfer.  It extends
  GoldbachLocalWheel with exact, hole-free arithmetic at the next local primes
  and the three-prime product wheel K₂K₃K₅.

  Contents (PROVED, unconditional, axiom-clean over Mathlib):
    * gCount specializations at p = 11, 13.
    * Exact K_p closed forms at p = 11, 13 on divisible / non-divisible shifts.
    * The three-prime finite wheel K235 = K₂ · K₃ · K₅ with full case table
      by (2|h, 3|h, 5|h) divisibility.
    * Exact finite inequalities: nonnegativity, max value 585/256, positivity
      exactly on even shifts, characterization of full 2–3–5 alignment.

  Imports: GoldbachComb, GoldbachLocalWheel, GoldbachParity, GoldbachLemmas only.

  Verification: AXLE `check` @ lean-4.32.0; #print axioms ⊆
  {propext, Classical.choice, Quot.sound}. No sorry / admit / axiom /
  native_decide.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachLocalWheel
import Brockian.GoldbachParity
import Brockian.GoldbachLemmas

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Brockian.Goldbach.WheelExtended

open Finset
open Brockian.GoldbachComb
open Brockian.Goldbach.LocalWheel
open Brockian.Goldbach.Parity
open Brockian.GoldbachLemmas

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by decide⟩
private instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by decide⟩

/-! ## Local Goldbach counts at p = 11, 13 -/

/-- Closed form of the local count at the prime 11. -/
theorem gCount_eleven (c : ZMod 11) : gCount 11 c = if c = 0 then 10 else 9 :=
  gCount_eq 11 c

/-- At `p = 11` and target `c = 0`, the local count is `10`. -/
theorem gCount_eleven_zero : gCount 11 (0 : ZMod 11) = 10 := by
  simp [gCount_eleven]

/-- At `p = 11` and nonzero target, the local count is `9`. -/
theorem gCount_eleven_of_ne_zero {c : ZMod 11} (hc : c ≠ 0) : gCount 11 c = 9 := by
  simp [gCount_eleven, hc]

/-- Residue-class candidate counts mod 11: `10` when residue 0, else `9`. -/
theorem gResidues_eleven_card (n : ZMod 11) :
    (gResidues 11 n).card = if n = 0 then 10 else 9 := by
  by_cases hn : n = 0
  · subst hn
    simp [gResidues_card_zero]
  · simp [gResidues_card_ne_zero hn, hn]

/-- Comb and Lemmas local counts agree at `p = 11`. -/
theorem gCount_eleven_eq_gResidues_card (c : ZMod 11) :
    gCount 11 c = (gResidues 11 c).card :=
  gCount_eq_gResidues_card 11 c

/-- Closed form of the local count at the prime 13. -/
theorem gCount_thirteen (c : ZMod 13) : gCount 13 c = if c = 0 then 12 else 11 :=
  gCount_eq 13 c

/-- At `p = 13` and target `c = 0`, the local count is `12`. -/
theorem gCount_thirteen_zero : gCount 13 (0 : ZMod 13) = 12 := by
  simp [gCount_thirteen]

/-- At `p = 13` and nonzero target, the local count is `11`. -/
theorem gCount_thirteen_of_ne_zero {c : ZMod 13} (hc : c ≠ 0) : gCount 13 c = 11 := by
  simp [gCount_thirteen, hc]

/-- Residue-class candidate counts mod 13: `12` when residue 0, else `11`. -/
theorem gResidues_thirteen_card (n : ZMod 13) :
    (gResidues 13 n).card = if n = 0 then 12 else 11 := by
  by_cases hn : n = 0
  · subst hn
    simp [gResidues_card_zero]
  · simp [gResidues_card_ne_zero hn, hn]

/-- Comb and Lemmas local counts agree at `p = 13`. -/
theorem gCount_thirteen_eq_gResidues_card (c : ZMod 13) :
    gCount 13 c = (gResidues 13 c).card :=
  gCount_eq_gResidues_card 13 c

/-! ## Exact local covariance factors at p = 11, 13 -/

/-- If `11 ∣ h`, the p = 11 local covariance factor is `1001/1000`. -/
theorem Kp_eleven_of_dvd {h : ℤ} (hh : (11 : ℤ) ∣ h) :
    Kp 11 h = (1001 / 1000 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `11 ∤ h`, the p = 11 local covariance factor is `9999/10000`. -/
theorem Kp_eleven_of_not_dvd {h : ℤ} (hh : ¬(11 : ℤ) ∣ h) :
    Kp 11 h = (9999 / 10000 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- Closed form: `K₁₁(h) = 1001/1000` if `11 ∣ h`, else `9999/10000`. -/
theorem Kp_eleven (h : ℤ) :
    Kp 11 h = if (11 : ℤ) ∣ h then (1001 / 1000 : ℚ) else (9999 / 10000 : ℚ) := by
  split_ifs with hh
  · exact Kp_eleven_of_dvd hh
  · exact Kp_eleven_of_not_dvd hh

/-- The p = 11 local covariance exceeds 1 exactly on `11`-divisible shifts. -/
theorem Kp_eleven_gt_one_iff (h : ℤ) :
    (1 : ℚ) < Kp 11 h ↔ (11 : ℤ) ∣ h := by
  constructor
  · intro hgt
    by_contra h11
    rw [Kp_eleven_of_not_dvd h11] at hgt
    norm_num at hgt
  · intro h11
    rw [Kp_eleven_of_dvd h11]
    norm_num

/-- Aligned p = 11 factor strictly exceeds the misaligned p = 11 factor. -/
theorem Kp_eleven_aligned_gt_misaligned {h₁ h₂ : ℤ}
    (h1 : (11 : ℤ) ∣ h₁) (h2 : ¬(11 : ℤ) ∣ h₂) :
    Kp 11 h₂ < Kp 11 h₁ := by
  rw [Kp_eleven_of_dvd h1, Kp_eleven_of_not_dvd h2]
  norm_num

/-- If `13 ∣ h`, the p = 13 local covariance factor is `1729/1728`. -/
theorem Kp_thirteen_of_dvd {h : ℤ} (hh : (13 : ℤ) ∣ h) :
    Kp 13 h = (1729 / 1728 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `13 ∤ h`, the p = 13 local covariance factor is `20735/20736`. -/
theorem Kp_thirteen_of_not_dvd {h : ℤ} (hh : ¬(13 : ℤ) ∣ h) :
    Kp 13 h = (20735 / 20736 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- Closed form: `K₁₃(h) = 1729/1728` if `13 ∣ h`, else `20735/20736`. -/
theorem Kp_thirteen (h : ℤ) :
    Kp 13 h = if (13 : ℤ) ∣ h then (1729 / 1728 : ℚ) else (20735 / 20736 : ℚ) := by
  split_ifs with hh
  · exact Kp_thirteen_of_dvd hh
  · exact Kp_thirteen_of_not_dvd hh

/-- The p = 13 local covariance exceeds 1 exactly on `13`-divisible shifts. -/
theorem Kp_thirteen_gt_one_iff (h : ℤ) :
    (1 : ℚ) < Kp 13 h ↔ (13 : ℤ) ∣ h := by
  constructor
  · intro hgt
    by_contra h13
    rw [Kp_thirteen_of_not_dvd h13] at hgt
    norm_num at hgt
  · intro h13
    rw [Kp_thirteen_of_dvd h13]
    norm_num

/-- Aligned p = 13 factor strictly exceeds the misaligned p = 13 factor. -/
theorem Kp_thirteen_aligned_gt_misaligned {h₁ h₂ : ℤ}
    (h1 : (13 : ℤ) ∣ h₁) (h2 : ¬(13 : ℤ) ∣ h₂) :
    Kp 13 h₂ < Kp 13 h₁ := by
  rw [Kp_thirteen_of_dvd h1, Kp_thirteen_of_not_dvd h2]
  norm_num

/-! ## The finite p = 2,3,5 covariance wheel -/

/-- The finite covariance product over the three local primes that control
parity, the mod-3 comb, and the next odd wheel factor. Exact finite arithmetic;
not a transfer claim. -/
def K235 (h : ℤ) : ℚ :=
  Kp 2 h * Kp 3 h * Kp 5 h

/-- Relates the three-prime wheel to the two-prime wheel of `LocalWheel`. -/
theorem K235_eq_K23_mul_Kp_five (h : ℤ) : K235 h = K23 h * Kp 5 h := by
  simp [K235, K23, mul_assoc]

/-- Odd shifts are killed by the p = 2 factor. -/
theorem K235_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) :
    K235 h = 0 := by
  simp [K235, Kp_two_of_not_dvd h2]

/-- Even, 3-divisible, 5-divisible shifts: fully aligned value `585/256`. -/
theorem K235_of_two_three_five_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : (3 : ℤ) ∣ h) (h5 : (5 : ℤ) ∣ h) :
    K235 h = (585 / 256 : ℚ) := by
  simp [K235, Kp_two_of_dvd h2, Kp_three_of_dvd h3, Kp_five_of_dvd h5]
  norm_num

/-- Even, 3-divisible, not 5-divisible: value `2295/1024`. -/
theorem K235_of_two_three_dvd_not_five {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : (3 : ℤ) ∣ h) (h5 : ¬(5 : ℤ) ∣ h) :
    K235 h = (2295 / 1024 : ℚ) := by
  simp [K235, Kp_two_of_dvd h2, Kp_three_of_dvd h3, Kp_five_of_not_dvd h5]
  norm_num

/-- Even, not 3-divisible, 5-divisible: value `975/512`. -/
theorem K235_of_two_five_dvd_not_three {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : ¬(3 : ℤ) ∣ h) (h5 : (5 : ℤ) ∣ h) :
    K235 h = (975 / 512 : ℚ) := by
  simp [K235, Kp_two_of_dvd h2, Kp_three_of_not_dvd h3, Kp_five_of_dvd h5]
  norm_num

/-- Even, neither 3- nor 5-divisible: baseline value `3825/2048`. -/
theorem K235_of_two_dvd_not_three_not_five {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : ¬(3 : ℤ) ∣ h) (h5 : ¬(5 : ℤ) ∣ h) :
    K235 h = (3825 / 2048 : ℚ) := by
  simp [K235, Kp_two_of_dvd h2, Kp_three_of_not_dvd h3, Kp_five_of_not_dvd h5]
  norm_num

/-- Closed form of the 2–3–5 wheel via the closed forms of `K₂`, `K₃`, `K₅`. -/
theorem K235_eq (h : ℤ) :
    K235 h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (3 : ℤ) ∣ h then (9 / 8 : ℚ) else (15 / 16 : ℚ)) *
      (if (5 : ℤ) ∣ h then (65 / 64 : ℚ) else (255 / 256 : ℚ)) := by
  simp [K235, Kp_two h, Kp_three h, Kp_five h]

/-- Case table: every divisibility pattern for the three-prime wheel. -/
theorem K235_cases (h : ℤ) :
    K235 h =
      if ¬(2 : ℤ) ∣ h then (0 : ℚ)
      else if (3 : ℤ) ∣ h then
        if (5 : ℤ) ∣ h then (585 / 256 : ℚ) else (2295 / 1024 : ℚ)
      else if (5 : ℤ) ∣ h then (975 / 512 : ℚ)
      else (3825 / 2048 : ℚ) := by
  by_cases h2 : (2 : ℤ) ∣ h
  · by_cases h3 : (3 : ℤ) ∣ h
    · by_cases h5 : (5 : ℤ) ∣ h
      · simp [h2, h3, h5, K235_of_two_three_five_dvd h2 h3 h5]
      · simp [h2, h3, h5, K235_of_two_three_dvd_not_five h2 h3 h5]
    · by_cases h5 : (5 : ℤ) ∣ h
      · simp [h2, h3, h5, K235_of_two_five_dvd_not_three h2 h3 h5]
      · simp [h2, h3, h5, K235_of_two_dvd_not_three_not_five h2 h3 h5]
  · simp [h2, K235_of_not_two_dvd h2]

/-! ## Nonnegativity and upper bounds for K235 -/

/-- The p = 2,3,5 product is nonnegative for every shift. -/
theorem K235_nonneg (h : ℤ) : 0 ≤ K235 h := by
  rw [K235_eq]
  split_ifs <;> norm_num

/-- The p = 2,3,5 product never exceeds the fully aligned value `585/256`. -/
theorem K235_le_aligned (h : ℤ) : K235 h ≤ (585 / 256 : ℚ) := by
  rw [K235_eq]
  split_ifs <;> norm_num

/-- The p = 2,3,5 product is positive exactly on even shifts. -/
theorem K235_pos_iff_two_dvd (h : ℤ) :
    0 < K235 h ↔ (2 : ℤ) ∣ h := by
  constructor
  · intro hpos
    by_contra h2
    rw [K235_of_not_two_dvd h2] at hpos
    exact (lt_irrefl (0 : ℚ) hpos)
  · intro h2
    by_cases h3 : (3 : ℤ) ∣ h
    · by_cases h5 : (5 : ℤ) ∣ h
      · rw [K235_of_two_three_five_dvd h2 h3 h5]; norm_num
      · rw [K235_of_two_three_dvd_not_five h2 h3 h5]; norm_num
    · by_cases h5 : (5 : ℤ) ∣ h
      · rw [K235_of_two_five_dvd_not_three h2 h3 h5]; norm_num
      · rw [K235_of_two_dvd_not_three_not_five h2 h3 h5]; norm_num

/-- Equality with the fully aligned value characterises simultaneous 2-, 3-, and
5-divisibility. -/
theorem K235_eq_aligned_iff (h : ℤ) :
    K235 h = (585 / 256 : ℚ) ↔ (2 : ℤ) ∣ h ∧ (3 : ℤ) ∣ h ∧ (5 : ℤ) ∣ h := by
  constructor
  · intro heq
    by_cases h2 : (2 : ℤ) ∣ h
    · by_cases h3 : (3 : ℤ) ∣ h
      · by_cases h5 : (5 : ℤ) ∣ h
        · exact ⟨h2, h3, h5⟩
        · rw [K235_of_two_three_dvd_not_five h2 h3 h5] at heq
          norm_num at heq
      · by_cases h5 : (5 : ℤ) ∣ h
        · rw [K235_of_two_five_dvd_not_three h2 h3 h5] at heq
          norm_num at heq
        · rw [K235_of_two_dvd_not_three_not_five h2 h3 h5] at heq
          norm_num at heq
    · rw [K235_of_not_two_dvd h2] at heq
      norm_num at heq
  · rintro ⟨h2, h3, h5⟩
    exact K235_of_two_three_five_dvd h2 h3 h5

/-- Relative to the even non-3 non-5 baseline `3825/2048`, the finite p = 2,3,5
predictor is strictly lifted exactly when at least one of 3 or 5 also divides. -/
theorem K235_above_even_baseline_iff (h : ℤ) :
    (3825 / 2048 : ℚ) < K235 h ↔
      (2 : ℤ) ∣ h ∧ ((3 : ℤ) ∣ h ∨ (5 : ℤ) ∣ h) := by
  constructor
  · intro hgt
    by_cases h2 : (2 : ℤ) ∣ h
    · refine ⟨h2, ?_⟩
      by_cases h3 : (3 : ℤ) ∣ h
      · exact Or.inl h3
      · by_cases h5 : (5 : ℤ) ∣ h
        · exact Or.inr h5
        · rw [K235_of_two_dvd_not_three_not_five h2 h3 h5] at hgt
          exact (lt_irrefl _ hgt).elim
    · rw [K235_of_not_two_dvd h2] at hgt
      norm_num at hgt
  · rintro ⟨h2, h35⟩
    rcases h35 with h3 | h5
    · by_cases h5' : (5 : ℤ) ∣ h
      · rw [K235_of_two_three_five_dvd h2 h3 h5']; norm_num
      · rw [K235_of_two_three_dvd_not_five h2 h3 h5']; norm_num
    · by_cases h3' : (3 : ℤ) ∣ h
      · rw [K235_of_two_three_five_dvd h2 h3' h5]; norm_num
      · rw [K235_of_two_five_dvd_not_three h2 h3' h5]; norm_num

/-- On even shifts the finite excess over the non-3 non-5 baseline is nonnegative. -/
theorem K235_excess_nonneg_of_even {h : ℤ} (h2 : (2 : ℤ) ∣ h) :
    0 ≤ K235 h - (3825 / 2048 : ℚ) := by
  by_cases h3 : (3 : ℤ) ∣ h
  · by_cases h5 : (5 : ℤ) ∣ h
    · rw [K235_of_two_three_five_dvd h2 h3 h5]; norm_num
    · rw [K235_of_two_three_dvd_not_five h2 h3 h5]; norm_num
  · by_cases h5 : (5 : ℤ) ∣ h
    · rw [K235_of_two_five_dvd_not_three h2 h3 h5]; norm_num
    · rw [K235_of_two_dvd_not_three_not_five h2 h3 h5]; norm_num

/-- Fully aligned three-prime wheel value strictly exceeds the even baseline. -/
theorem K235_aligned_gt_baseline : (3825 / 2048 : ℚ) < (585 / 256 : ℚ) := by
  norm_num

/-- Fully aligned three-prime value strictly exceeds the two-prime aligned value
`9/4` (because the aligned p = 5 factor is `65/64 > 1`). -/
theorem K235_aligned_gt_K23_aligned : (9 / 4 : ℚ) < (585 / 256 : ℚ) := by
  norm_num

/-- Single-factor nonnegativity: every odd-prime local covariance factor is positive. -/
theorem Kp_eleven_pos (h : ℤ) : 0 < Kp 11 h := by
  rw [Kp_eleven]
  split_ifs <;> norm_num

/-- Single-factor nonnegativity at p = 13. -/
theorem Kp_thirteen_pos (h : ℤ) : 0 < Kp 13 h := by
  rw [Kp_thirteen]
  split_ifs <;> norm_num

/-- Upper bound for the p = 11 factor: never exceeds the aligned value. -/
theorem Kp_eleven_le_aligned (h : ℤ) : Kp 11 h ≤ (1001 / 1000 : ℚ) := by
  rw [Kp_eleven]
  split_ifs <;> norm_num

/-- Upper bound for the p = 13 factor: never exceeds the aligned value. -/
theorem Kp_thirteen_le_aligned (h : ℤ) : Kp 13 h ≤ (1729 / 1728 : ℚ) := by
  rw [Kp_thirteen]
  split_ifs <;> norm_num

end Brockian.Goldbach.WheelExtended
