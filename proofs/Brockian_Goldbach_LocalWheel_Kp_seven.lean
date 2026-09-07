/-
  Brockian/GoldbachLocalWheel.lean — finite local Goldbach wheel facts.

  HONEST SCOPE: this module does NOT prove the Goldbach conjecture, does not
  assert a global representation theorem for even integers, and does not claim
  the empirical/asymptotic Goldbach residual transfer.  It records exact,
  hole-free arithmetic about the local count g_p and the local covariance
  factors K_p at the small primes that control the mod-2 / mod-3 wheel, plus
  exact finite predictor inequalities for the product K₂K₃.

  Contents (PROVED, unconditional, axiom-clean over Mathlib):
    * gCount specializations at p = 3, 7.
    * Exact K_p values at p = 3, 5, 7 on divisible / non-divisible shifts.
    * The two-prime finite wheel K23 = K₂ · K₃ with support statements.
    * Exact finite inequalities: nonnegativity, max value 9/4, lift over the
      even non-3 baseline 15/8.
    * local_covariance specializations at p = 2 and p = 3.

  Imports: GoldbachComb, GoldbachParity, GoldbachLemmas only.

  Verification: AXLE `check` @ lean-4.32.0; #print axioms ⊆
  {propext, Classical.choice, Quot.sound}. No sorry / admit / axiom /
  native_decide.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity
import Brockian.GoldbachLemmas

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Brockian.Goldbach.LocalWheel

open Finset
open Brockian.GoldbachComb
open Brockian.Goldbach.Parity
open Brockian.GoldbachLemmas

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ## Local Goldbach counts at small odd primes -/

/-- At `p = 3` and target `c = 0`, the local count is `2`. -/
theorem gCount_three_zero : gCount 3 (0 : ZMod 3) = 2 := by
  simp [gCount_eq]

/-- At `p = 3` and nonzero target, the local count is `1`. -/
theorem gCount_three_of_ne_zero {c : ZMod 3} (hc : c ≠ 0) : gCount 3 c = 1 := by
  simp [gCount_eq, hc]

/-- Closed form of the local count at the prime 3. -/
theorem gCount_three (c : ZMod 3) : gCount 3 c = if c = 0 then 2 else 1 :=
  gCount_eq 3 c

/-- Residue-class candidate counts mod 3: `2` when residue 0, else `1`. -/
theorem gResidues_three_card (n : ZMod 3) :
    (gResidues 3 n).card = if n = 0 then 2 else 1 := by
  by_cases hn : n = 0
  · subst hn
    simp [gResidues_card_zero]
  · simp [gResidues_card_ne_zero hn, hn]

/-- Comb and Lemmas local counts agree at `p = 3`. -/
theorem gCount_three_eq_gResidues_card (c : ZMod 3) :
    gCount 3 c = (gResidues 3 c).card :=
  gCount_eq_gResidues_card 3 c

/-- Closed form of the local count at the prime 7. -/
theorem gCount_seven (c : ZMod 7) : gCount 7 c = if c = 0 then 6 else 5 :=
  gCount_eq 7 c

/-- At `p = 7` and target `c = 0`, the local count is `6`. -/
theorem gCount_seven_zero : gCount 7 (0 : ZMod 7) = 6 := by
  simp [gCount_seven]

/-- At `p = 7` and nonzero target, the local count is `5`. -/
theorem gCount_seven_of_ne_zero {c : ZMod 7} (hc : c ≠ 0) : gCount 7 c = 5 := by
  simp [gCount_seven, hc]

/-! ## Exact local covariance factors at small primes -/

/-- If `3 ∣ h`, the p = 3 local covariance factor is `9/8`. -/
theorem Kp_three_of_dvd {h : ℤ} (hh : (3 : ℤ) ∣ h) :
    Kp 3 h = (9 / 8 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `3 ∤ h`, the p = 3 local covariance factor is `15/16`. -/
theorem Kp_three_of_not_dvd {h : ℤ} (hh : ¬(3 : ℤ) ∣ h) :
    Kp 3 h = (15 / 16 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- Closed form: `K₃(h) = 9/8` if `3 ∣ h`, else `15/16`. -/
theorem Kp_three (h : ℤ) :
    Kp 3 h = if (3 : ℤ) ∣ h then (9 / 8 : ℚ) else (15 / 16 : ℚ) := by
  split_ifs with hh
  · exact Kp_three_of_dvd hh
  · exact Kp_three_of_not_dvd hh

/-- The p = 3 local covariance exceeds 1 exactly on `3`-divisible shifts. -/
theorem Kp_three_gt_one_iff (h : ℤ) :
    (1 : ℚ) < Kp 3 h ↔ (3 : ℤ) ∣ h := by
  constructor
  · intro hgt
    by_contra h3
    rw [Kp_three_of_not_dvd h3] at hgt
    norm_num at hgt
  · intro h3
    rw [Kp_three_of_dvd h3]
    norm_num

/-- Aligned p = 3 factor strictly exceeds the misaligned p = 3 factor. -/
theorem Kp_three_aligned_gt_misaligned {h₁ h₂ : ℤ}
    (h1 : (3 : ℤ) ∣ h₁) (h2 : ¬(3 : ℤ) ∣ h₂) :
    Kp 3 h₂ < Kp 3 h₁ := by
  rw [Kp_three_of_dvd h1, Kp_three_of_not_dvd h2]
  norm_num

/-- If `5 ∣ h`, the p = 5 local covariance factor is `65/64`. -/
theorem Kp_five_of_dvd {h : ℤ} (hh : (5 : ℤ) ∣ h) :
    Kp 5 h = (65 / 64 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `5 ∤ h`, the p = 5 local covariance factor is `255/256`. -/
theorem Kp_five_of_not_dvd {h : ℤ} (hh : ¬(5 : ℤ) ∣ h) :
    Kp 5 h = (255 / 256 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- Closed form: `K₅(h) = 65/64` if `5 ∣ h`, else `255/256`. -/
theorem Kp_five (h : ℤ) :
    Kp 5 h = if (5 : ℤ) ∣ h then (65 / 64 : ℚ) else (255 / 256 : ℚ) := by
  split_ifs with hh
  · exact Kp_five_of_dvd hh
  · exact Kp_five_of_not_dvd hh

/-- If `7 ∣ h`, the p = 7 local covariance factor is `217/216`. -/
theorem Kp_seven_of_dvd {h : ℤ} (hh : (7 : ℤ) ∣ h) :
    Kp 7 h = (217 / 216 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- If `7 ∤ h`, the p = 7 local covariance factor is `1295/1296`. -/
theorem Kp_seven_of_not_dvd {h : ℤ} (hh : ¬(7 : ℤ) ∣ h) :
    Kp 7 h = (1295 / 1296 : ℚ) := by
  simp [Kp, hh]
  norm_num

/-- Closed form: `K₇(h) = 217/216` if `7 ∣ h`, else `1295/1296`. -/
theorem Kp_seven (h : ℤ) :
    Kp 7 h = if (7 : ℤ) ∣ h then (217 / 216 : ℚ) else (1295 / 1296 : ℚ) := by
  split_ifs with hh
  · exact Kp_seven_of_dvd hh
  · exact Kp_seven_of_not_dvd hh

/-! ## The finite p = 2,3 covariance wheel -/

/-- The finite covariance product over the two local primes that control parity
and the observed mod-3 comb. Exact finite arithmetic; not a transfer claim. -/
def K23 (h : ℤ) : ℚ :=
  Kp 2 h * Kp 3 h

/-- Odd shifts are killed by the p = 2 factor. -/
theorem K23_of_not_two_dvd {h : ℤ} (h2 : ¬(2 : ℤ) ∣ h) :
    K23 h = 0 := by
  simp [K23, Kp_two_of_not_dvd h2]

/-- Even, 3-divisible shifts have finite p = 2,3 value `9/4`. -/
theorem K23_of_two_dvd_three_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : (3 : ℤ) ∣ h) :
    K23 h = (9 / 4 : ℚ) := by
  simp [K23, Kp_two_of_dvd h2, Kp_three_of_dvd h3]
  norm_num

/-- Even shifts not divisible by `3` have finite p = 2,3 value `15/8`. -/
theorem K23_of_two_dvd_not_three_dvd {h : ℤ}
    (h2 : (2 : ℤ) ∣ h) (h3 : ¬(3 : ℤ) ∣ h) :
    K23 h = (15 / 8 : ℚ) := by
  simp [K23, Kp_two_of_dvd h2, Kp_three_of_not_dvd h3]
  norm_num

/-- Closed form of the 2–3 wheel via the closed forms of `K₂` and `K₃`. -/
theorem K23_eq (h : ℤ) :
    K23 h = (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if (3 : ℤ) ∣ h then (9 / 8 : ℚ) else (15 / 16 : ℚ)) := by
  simp [K23, Kp_two h, Kp_three h]

/-- The p = 2,3 product is nonnegative for every shift. -/
theorem K23_nonneg (h : ℤ) : 0 ≤ K23 h := by
  rw [K23_eq]
  split_ifs <;> norm_num

/-- The p = 2,3 product never exceeds the fully aligned value `9/4`. -/
theorem K23_le_nine_quarters (h : ℤ) : K23 h ≤ (9 / 4 : ℚ) := by
  rw [K23_eq]
  split_ifs <;> norm_num

/-- The p = 2,3 product is positive exactly on even shifts. -/
theorem K23_pos_iff_two_dvd (h : ℤ) :
    0 < K23 h ↔ (2 : ℤ) ∣ h := by
  constructor
  · intro hpos
    by_contra h2
    rw [K23_of_not_two_dvd h2] at hpos
    exact (lt_irrefl (0 : ℚ) hpos)
  · intro h2
    by_cases h3 : (3 : ℤ) ∣ h
    · rw [K23_of_two_dvd_three_dvd h2 h3]; norm_num
    · rw [K23_of_two_dvd_not_three_dvd h2 h3]; norm_num

/-- Relative to the even non-3 baseline `15/8`, the finite p = 2,3 predictor
is strictly lifted exactly when both local factors align. -/
theorem K23_above_even_nonthree_baseline_iff (h : ℤ) :
    (15 / 8 : ℚ) < K23 h ↔ (2 : ℤ) ∣ h ∧ (3 : ℤ) ∣ h := by
  constructor
  · intro hgt
    by_cases h2 : (2 : ℤ) ∣ h
    · refine ⟨h2, ?_⟩
      by_contra h3
      rw [K23_of_two_dvd_not_three_dvd h2 h3] at hgt
      exact (lt_irrefl _ hgt)
    · rw [K23_of_not_two_dvd h2] at hgt
      norm_num at hgt
  · rintro ⟨h2, h3⟩
    rw [K23_of_two_dvd_three_dvd h2 h3]
    norm_num

/-- Equality with the fully aligned value characterises simultaneous 2- and
3-divisibility. -/
theorem K23_eq_nine_quarters_iff (h : ℤ) :
    K23 h = (9 / 4 : ℚ) ↔ (2 : ℤ) ∣ h ∧ (3 : ℤ) ∣ h := by
  constructor
  · intro heq
    by_cases h2 : (2 : ℤ) ∣ h
    · refine ⟨h2, ?_⟩
      by_contra h3
      rw [K23_of_two_dvd_not_three_dvd h2 h3] at heq
      norm_num at heq
    · rw [K23_of_not_two_dvd h2] at heq
      norm_num at heq
  · rintro ⟨h2, h3⟩
    exact K23_of_two_dvd_three_dvd h2 h3

/-- On even shifts the finite excess over the non-3 baseline `15/8` is
nonnegative. -/
theorem K23_excess_nonneg_of_even {h : ℤ} (h2 : (2 : ℤ) ∣ h) :
    0 ≤ K23 h - (15 / 8 : ℚ) := by
  by_cases h3 : (3 : ℤ) ∣ h
  · rw [K23_of_two_dvd_three_dvd h2 h3]; norm_num
  · rw [K23_of_two_dvd_not_three_dvd h2 h3]; norm_num

/-- The finite excess over `15/8` is positive exactly on simultaneous 2- and
3-divisible shifts. -/
theorem K23_excess_pos_iff (h : ℤ) :
    0 < K23 h - (15 / 8 : ℚ) ↔ (2 : ℤ) ∣ h ∧ (3 : ℤ) ∣ h := by
  constructor
  · intro hpos
    exact (K23_above_even_nonthree_baseline_iff h).mp (sub_pos.mp hpos)
  · intro halign
    exact sub_pos.mpr ((K23_above_even_nonthree_baseline_iff h).mpr halign)

/-- Fully aligned wheel value strictly exceeds the even non-3 baseline. -/
theorem K23_aligned_gt_baseline : (15 / 8 : ℚ) < (9 / 4 : ℚ) := by
  norm_num

/-! ## local_covariance specializations (via GoldbachComb) -/

/-- At `p = 2` and zero shift, the local mean product equals `1/2`. -/
theorem local_covariance_two_zero :
    (∑ c : ZMod 2, (gCount 2 c : ℚ) * gCount 2 (c + 0)) / 2 = (1 / 2 : ℚ) := by
  have h := local_covariance (p := 2) (0 : ZMod 2)
  -- RHS of `local_covariance` at h=0 is ((2-1)²/2)² · K₂(0) = (1/2)² · 2 = 1/2.
  simp [Kp] at h
  exact h.trans (by norm_num)

/-- At `p = 2` and nonzero shift, the local mean product vanishes. -/
theorem local_covariance_two_ne_zero {h : ZMod 2} (hh : h ≠ 0) :
    (∑ c : ZMod 2, (gCount 2 c : ℚ) * gCount 2 (c + h)) / 2 = (0 : ℚ) := by
  have hcov := local_covariance (p := 2) h
  -- RHS: ((2-1)²/2)² · K₂(1) = (1/4) · 0 = 0.
  simp [Kp, hh] at hcov
  exact hcov.trans (by norm_num)

/-- At `p = 3` and zero shift, the local mean product equals `2`. -/
theorem local_covariance_three_zero :
    (∑ c : ZMod 3, (gCount 3 c : ℚ) * gCount 3 (c + 0)) / 3 = (2 : ℚ) := by
  have h := local_covariance (p := 3) (0 : ZMod 3)
  -- RHS: ((3-1)²/3)² · K₃(0) = (4/3)² · (9/8) = 2.
  simp [Kp] at h
  exact h.trans (by norm_num)

/-- At `p = 3` and nonzero shift, the local mean product equals `5/3`. -/
theorem local_covariance_three_ne_zero {h : ZMod 3} (hh : h ≠ 0) :
    (∑ c : ZMod 3, (gCount 3 c : ℚ) * gCount 3 (c + h)) / 3 = (5 / 3 : ℚ) := by
  have hcov := local_covariance (p := 3) h
  -- RHS: ((3-1)²/3)² · K₃(1) = (4/3)² · (15/16) = 5/3.
  simp [Kp, hh] at hcov
  exact hcov.trans (by norm_num)

/-- Zero-shift local covariance at `p = 3` strictly exceeds any nonzero-shift value. -/
theorem local_covariance_three_zero_gt_ne_zero {h : ZMod 3} (hh : h ≠ 0) :
    (∑ c : ZMod 3, (gCount 3 c : ℚ) * gCount 3 (c + h)) / 3 <
      (∑ c : ZMod 3, (gCount 3 c : ℚ) * gCount 3 (c + 0)) / 3 := by
  rw [local_covariance_three_ne_zero hh, local_covariance_three_zero]
  norm_num

end Brockian.Goldbach.LocalWheel
