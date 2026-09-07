/-
  Brockian/GoldbachCovarianceScaffold.lean

  Honest disassembly of the remaining Goldbach covariance-transfer claim.

  This module does not prove Goldbach and does not assert the empirical/asymptotic
  transfer from the finite covariance kernel to the Goldbach residual.  It proves
  local, finite, unconditional arithmetic around the already-verified comb kernel:

    * exact p = 3 covariance values and the 3-divisibility excess criterion;
    * exact p = 2 parity support and the two-prime finite wheel `K23`;
    * a positive-scale finite predictor lemma;
    * admissibility, hence finite singular-series product positivity, for the
      two-point tuple `{0,n}` when `n` is even.

  These are input lemmas for a future faithful replacement of
  `GoldbachComb.GoldbachCovarianceTransfer`; they are not the transfer theorem.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity
import Brockian.SingularSeries

set_option autoImplicit false

namespace Brockian.Goldbach.CovarianceScaffold

open Finset
open Brockian.GoldbachComb
open Brockian.Goldbach.Parity
open Brockian.SingularSeries

/-! ## Exact local covariance at p = 3 -/

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

/-- The p = 3 local covariance exceeds its neutral value exactly on
`3`-divisible shifts. -/
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

/-- The centered p = 3 excess is positive exactly on `3`-divisible shifts. -/
theorem Kp_three_excess_pos_iff (h : ℤ) :
    0 < Kp 3 h - 1 ↔ (3 : ℤ) ∣ h := by
  constructor
  · intro hpos
    exact (Kp_three_gt_one_iff h).mp (by linarith)
  · intro h3
    have hgt : (1 : ℚ) < Kp 3 h := (Kp_three_gt_one_iff h).mpr h3
    linarith

/-- The centered p = 3 excess is negative exactly off `3`-divisible shifts. -/
theorem Kp_three_excess_neg_iff (h : ℤ) :
    Kp 3 h - 1 < 0 ↔ ¬(3 : ℤ) ∣ h := by
  constructor
  · intro hneg h3
    rw [Kp_three_of_dvd h3] at hneg
    norm_num at hneg
  · intro h3
    rw [Kp_three_of_not_dvd h3]
    norm_num

/-! ## Exact parity support at p = 2 -/

/-- The p = 2 covariance factor is positive exactly on even shifts. -/
theorem Kp_two_pos_iff (h : ℤ) :
    0 < Kp 2 h ↔ (2 : ℤ) ∣ h := by
  constructor
  · intro hpos
    by_contra h2
    rw [Kp_two_of_not_dvd h2] at hpos
    norm_num at hpos
  · intro h2
    rw [Kp_two_of_dvd h2]
    norm_num

/-- The p = 2 factor vanishes exactly on odd shifts. -/
theorem Kp_two_eq_zero_iff (h : ℤ) :
    Kp 2 h = 0 ↔ ¬(2 : ℤ) ∣ h := by
  constructor
  · intro hz h2
    rw [Kp_two_of_dvd h2] at hz
    norm_num at hz
  · intro h2
    exact Kp_two_of_not_dvd h2

/-! ## The finite p = 2,3 covariance wheel -/

/-- The finite covariance product over the two local primes that control parity
and the observed mod-3 comb. -/
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

/-- The p = 2,3 product is positive exactly on even shifts. -/
theorem K23_pos_iff_two_dvd (h : ℤ) :
    0 < K23 h ↔ (2 : ℤ) ∣ h := by
  constructor
  · intro hpos
    by_contra h2
    rw [K23_of_not_two_dvd h2] at hpos
    norm_num at hpos
  · intro h2
    by_cases h3 : (3 : ℤ) ∣ h
    · rw [K23_of_two_dvd_three_dvd h2 h3]
      norm_num
    · rw [K23_of_two_dvd_not_three_dvd h2 h3]
      norm_num

/-- Relative to the even non-3 baseline `15/8`, the finite p = 2,3 predictor
is strictly lifted exactly when both local obstructions align. -/
theorem K23_above_even_nonthree_baseline_iff (h : ℤ) :
    (15 / 8 : ℚ) < K23 h ↔ (2 : ℤ) ∣ h ∧ (3 : ℤ) ∣ h := by
  constructor
  · intro hgt
    have h2 : (2 : ℤ) ∣ h := by
      by_contra h2
      rw [K23_of_not_two_dvd h2] at hgt
      norm_num at hgt
    refine ⟨h2, ?_⟩
    by_contra h3
    rw [K23_of_two_dvd_not_three_dvd h2 h3] at hgt
    norm_num at hgt
  · rintro ⟨h2, h3⟩
    rw [K23_of_two_dvd_three_dvd h2 h3]
    norm_num

/-! ## Positive-scale finite predictor -/

/-- A finite, explicitly scaled p = 2,3 excess predictor.  This is only a
deterministic arithmetic predictor; it is not a statement about Goldbach
residuals. -/
noncomputable def scaledK23Excess (β : ℕ → ℝ) (X : ℕ) (h : ℤ) : ℝ :=
  β X * ((K23 h : ℝ) - (15 / 8 : ℝ))

/-- With a positive scale, the finite predictor is positive exactly on shifts
where the p = 2 and p = 3 local factors both align. -/
theorem scaledK23Excess_pos_iff {β : ℕ → ℝ} (hβ : ∀ X : ℕ, 0 < β X)
    (X : ℕ) (h : ℤ) :
    0 < scaledK23Excess β X h ↔ (2 : ℤ) ∣ h ∧ (3 : ℤ) ∣ h := by
  unfold scaledK23Excess
  by_cases h2 : (2 : ℤ) ∣ h
  · by_cases h3 : (3 : ℤ) ∣ h
    · rw [K23_of_two_dvd_three_dvd h2 h3]
      constructor
      · intro _
        exact ⟨h2, h3⟩
      · intro _
        norm_num
        nlinarith [hβ X]
    · rw [K23_of_two_dvd_not_three_dvd h2 h3]
      constructor
      · intro hpos
        norm_num at hpos
      · rintro ⟨_, h3'⟩
        exact (h3 h3').elim
  · rw [K23_of_not_two_dvd h2]
    constructor
    · intro hpos
      norm_num at hpos
      nlinarith [hβ X]
    · rintro ⟨h2', _⟩
      exact (h2 h2').elim

/-! ## Singular-series input for the binary tuple `{0,n}` -/

/-- The two-point tuple attached to an even binary Goldbach target. -/
def goldbachPairTuple (n : ℕ) : Finset ℕ :=
  {0, n}

/-- The tuple `{0,n}` has cardinality at most two. -/
theorem goldbachPairTuple_card_le_two (n : ℕ) :
    (goldbachPairTuple n).card ≤ 2 := by
  unfold goldbachPairTuple
  exact Finset.card_le_two

/-- If `n` is even, the two-point tuple `{0,n}` has no local obstruction:
at `p = 2` both points collapse to residue `0`, and at odd primes a two-point
set cannot cover all residues. -/
theorem goldbachPairTuple_raw_admissible_of_even {n : ℕ} (hn : Even n) :
    ∀ p : ℕ, Nat.Prime p → nu_p (goldbachPairTuple n) p < p := by
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    have hdiv : 2 ∣ n := by
      rwa [even_iff_two_dvd] at hn
    have hnmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hsubset :
        (goldbachPairTuple n).image (fun x : ℕ => x % 2) ⊆ ({0} : Finset ℕ) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simp [goldbachPairTuple] at ha ⊢
      rcases ha with rfl | rfl
      · simp
      · exact hnmod
    unfold nu_p
    calc
      ((goldbachPairTuple n).image (fun x : ℕ => x % 2)).card
          ≤ ({0} : Finset ℕ).card := Finset.card_le_card hsubset
      _ < 2 := by simp
  · have hpgt : 2 < p := by
      have hp2le : 2 ≤ p := hp.two_le
      omega
    unfold nu_p
    exact lt_of_le_of_lt
      (le_trans Finset.card_image_le (goldbachPairTuple_card_le_two n)) hpgt

/-- Consequently, every finite singular-series product attached to `{0,n}` is
strictly positive for even `n`.  This is finite Euler-product arithmetic, not a
Goldbach representation theorem and not the infinite asymptotic transfer. -/
theorem singular_series_finite_goldbachPairTuple_pos_of_even {n : ℕ} (hn : Even n)
    (P : ℕ) :
    0 < singularSeriesFinite (goldbachPairTuple n) P :=
  singular_series_finite_pos (goldbachPairTuple n) P
    (goldbachPairTuple_raw_admissible_of_even hn)

end Brockian.Goldbach.CovarianceScaffold
