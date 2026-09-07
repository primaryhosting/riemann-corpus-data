/-
  Brockian/EquidistributionDeviationBound.lean

  Honest finite-range deviation bounds for the conditional equidistribution lane.

  This module does not assert Hardy-Littlewood, Bombieri-Vinogradov, or prime-pair
  equidistribution. It starts from an explicit `PrimePairAsymptotic q g` hypothesis
  and an explicit finite error budget on a finite window, then proves the resulting
  finite normalized deviation inequalities.

  The point is to make "finite range deviation bound" citable as a conditional
  bookkeeping theorem, with all analytic input still visible in the hypotheses.
-/
import Brockian.EquidistributionFiniteScaffold

set_option autoImplicit false

open Finset
open Brockian.Admissibility

namespace Brockian.Equidistribution.DeviationBound

/-! ## Direct finite deviation bounds from the asymptotic package -/

/-- The per-configuration finite deviation bound is exactly the finite field
provided by `PrimePairAsymptotic`, repackaged under a stable downstream name. -/
theorem perConfig_deviation_le_err
    {q : ℕ} [NeZero q] {g : ℕ}
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) (N : ℕ) :
    |(Brockian.Equidistribution.configCount N q g a : ℝ)
        - H.C * H.mainTerm N / ((q : ℝ) - 2)| ≤ H.err N :=
  Brockian.Equidistribution.FiniteScaffold.configCount_deviation_bound H ha N

/-- Summing the per-configuration finite bounds over the `q - 2` admissible
classes gives a total-count finite deviation bound. This is finite bookkeeping
under the explicit `PrimePairAsymptotic` hypothesis. -/
theorem totalConfig_deviation_le_scaled_err
    {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 < q)
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g) (N : ℕ) :
    |(Brockian.Equidistribution.totalConfigCount N q g : ℝ) - H.C * H.mainTerm N|
      ≤ ((q : ℝ) - 2) * H.err N :=
  Brockian.Equidistribution.FiniteScaffold.totalConfigCount_deviation_bound hq H N

/-- If the finite search window has no small-prime edge effects, the same total
deviation bound applies to the honest prime-pair count `pairCount`. The largeness
hypothesis is explicit and finite; no asymptotic distribution is claimed. -/
theorem pairCount_deviation_le_scaled_err_of_large_pairs
    {N q g : ℕ} [NeZero q] (hq : 2 < q)
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    (hlarge : ∀ p, p ≤ N → Nat.Prime p → Nat.Prime (p + g) → q < p ∧ q < p + g) :
    |(Brockian.Equidistribution.FiniteScaffold.pairCount N g : ℝ) - H.C * H.mainTerm N|
      ≤ ((q : ℝ) - 2) * H.err N := by
  have hqle : 2 ≤ q := le_of_lt hq
  have htotal :
      Brockian.Equidistribution.totalConfigCount N q g
        = Brockian.Equidistribution.FiniteScaffold.pairCount N g :=
    Brockian.Equidistribution.FiniteScaffold.totalConfigCount_eq_pairCount_of_large_pairs
      hqle hlarge
  simpa [htotal] using totalConfig_deviation_le_scaled_err hq H N

/-! ## Explicit finite-window error budgets -/

/-- A finite error budget for a fixed `PrimePairAsymptotic`: on the window
`N0 ≤ N ≤ N1`, the main term is positive and the error is at most
`ε * mainTerm N`. This is the place to plug in an empirical or conditional finite
range hypothesis such as `ε = 1 / 3`; the structure itself proves no such estimate. -/
structure FiniteRangeErrorBudget
    {q : ℕ} [NeZero q] {g : ℕ}
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    (N0 N1 : ℕ) (ε : ℝ) : Prop where
  /-- The advertised finite error level is nonnegative. -/
  epsilon_nonneg : 0 ≤ ε
  /-- Main terms are positive throughout the finite window. -/
  main_pos : ∀ N, N0 ≤ N → N ≤ N1 → 0 < H.mainTerm N
  /-- The error is bounded by `ε` times the main term throughout the window. -/
  err_le_epsilon_main : ∀ N, N0 ≤ N → N ≤ N1 → H.err N ≤ ε * H.mainTerm N

/-- Under a finite error budget, every admissible configuration has normalized
finite deviation at most `ε` on the specified window. -/
theorem perConfig_normalized_deviation_le_epsilon
    {q : ℕ} [NeZero q] {g N0 N1 : ℕ} {ε : ℝ}
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    (B : FiniteRangeErrorBudget H N0 N1 ε)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q))
    {N : ℕ} (hN0 : N0 ≤ N) (hN1 : N ≤ N1) :
    |((Brockian.Equidistribution.configCount N q g a : ℝ) / H.mainTerm N)
        - H.C / ((q : ℝ) - 2)| ≤ ε := by
  have hmain_pos : 0 < H.mainTerm N := B.main_pos N hN0 hN1
  have hmain_ne : H.mainTerm N ≠ 0 := ne_of_gt hmain_pos
  have hbound := perConfig_deviation_le_err H ha N
  have herr := B.err_le_epsilon_main N hN0 hN1
  have hscaled :
      |(Brockian.Equidistribution.configCount N q g a : ℝ)
          - H.C * H.mainTerm N / ((q : ℝ) - 2)| / H.mainTerm N ≤ ε := by
    calc
      |(Brockian.Equidistribution.configCount N q g a : ℝ)
          - H.C * H.mainTerm N / ((q : ℝ) - 2)| / H.mainTerm N
          ≤ H.err N / H.mainTerm N := by
            exact div_le_div_of_nonneg_right hbound (le_of_lt hmain_pos)
      _ ≤ (ε * H.mainTerm N) / H.mainTerm N := by
            exact div_le_div_of_nonneg_right herr (le_of_lt hmain_pos)
      _ = ε := by
            exact mul_div_cancel_right₀ ε hmain_ne
  have hrewrite :
      ((Brockian.Equidistribution.configCount N q g a : ℝ) / H.mainTerm N)
          - H.C / ((q : ℝ) - 2)
        =
      ((Brockian.Equidistribution.configCount N q g a : ℝ)
          - H.C * H.mainTerm N / ((q : ℝ) - 2)) / H.mainTerm N := by
    field_simp [hmain_ne]
  rw [hrewrite, abs_div, abs_of_pos hmain_pos]
  exact hscaled

/-- Under a finite error budget, the admissible total count has normalized finite
deviation at most `(q - 2) * ε` on the specified window. -/
theorem totalConfig_normalized_deviation_le_scaled_epsilon
    {q : ℕ} [NeZero q] {g N0 N1 : ℕ} {ε : ℝ} (hq : 2 < q)
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    (B : FiniteRangeErrorBudget H N0 N1 ε)
    {N : ℕ} (hN0 : N0 ≤ N) (hN1 : N ≤ N1) :
    |((Brockian.Equidistribution.totalConfigCount N q g : ℝ) / H.mainTerm N) - H.C|
      ≤ ((q : ℝ) - 2) * ε := by
  have hmain_pos : 0 < H.mainTerm N := B.main_pos N hN0 hN1
  have hmain_ne : H.mainTerm N ≠ 0 := ne_of_gt hmain_pos
  have hscale_nonneg : 0 ≤ ((q : ℝ) - 2) := by
    have hqR : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  have hbound := totalConfig_deviation_le_scaled_err hq H N
  have herr := B.err_le_epsilon_main N hN0 hN1
  have hscaled :
      |(Brockian.Equidistribution.totalConfigCount N q g : ℝ) - H.C * H.mainTerm N|
          / H.mainTerm N
        ≤ ((q : ℝ) - 2) * ε := by
    calc
      |(Brockian.Equidistribution.totalConfigCount N q g : ℝ) - H.C * H.mainTerm N|
          / H.mainTerm N
          ≤ (((q : ℝ) - 2) * H.err N) / H.mainTerm N := by
            exact div_le_div_of_nonneg_right hbound (le_of_lt hmain_pos)
      _ ≤ (((q : ℝ) - 2) * (ε * H.mainTerm N)) / H.mainTerm N := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left herr hscale_nonneg) (le_of_lt hmain_pos)
      _ = ((q : ℝ) - 2) * ε := by
            rw [← mul_assoc]
            exact mul_div_cancel_right₀ (((q : ℝ) - 2) * ε) hmain_ne
  have hrewrite :
      ((Brockian.Equidistribution.totalConfigCount N q g : ℝ) / H.mainTerm N) - H.C
        =
      ((Brockian.Equidistribution.totalConfigCount N q g : ℝ) - H.C * H.mainTerm N)
        / H.mainTerm N := by
    field_simp [hmain_ne]
  rw [hrewrite, abs_div, abs_of_pos hmain_pos]
  exact hscaled

/-- The same normalized total finite deviation bound, transferred to the honest
prime-pair count under an explicit finite no-small-prime-edge-effects hypothesis. -/
theorem pairCount_normalized_deviation_le_scaled_epsilon_of_large_pairs
    {N q g N0 N1 : ℕ} [NeZero q] {ε : ℝ} (hq : 2 < q)
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    (B : FiniteRangeErrorBudget H N0 N1 ε)
    (hlarge : ∀ p, p ≤ N → Nat.Prime p → Nat.Prime (p + g) → q < p ∧ q < p + g)
    (hN0 : N0 ≤ N) (hN1 : N ≤ N1) :
    |((Brockian.Equidistribution.FiniteScaffold.pairCount N g : ℝ) / H.mainTerm N) - H.C|
      ≤ ((q : ℝ) - 2) * ε := by
  have hqle : 2 ≤ q := le_of_lt hq
  have htotal :
      Brockian.Equidistribution.totalConfigCount N q g
        = Brockian.Equidistribution.FiniteScaffold.pairCount N g :=
    Brockian.Equidistribution.FiniteScaffold.totalConfigCount_eq_pairCount_of_large_pairs
      hqle hlarge
  simpa [htotal] using
    totalConfig_normalized_deviation_le_scaled_epsilon hq H B hN0 hN1

/-- A named specialization for the common finite `1/3` error budget: if the
explicit finite-window budget holds with `ε = 1/3`, the normalized per-config
deviation is at most `1/3`. This is a conditional finite inequality only. -/
theorem perConfig_normalized_deviation_le_one_third
    {q : ℕ} [NeZero q] {g N0 N1 : ℕ}
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    (B : FiniteRangeErrorBudget H N0 N1 (1 / 3 : ℝ))
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q))
    {N : ℕ} (hN0 : N0 ≤ N) (hN1 : N ≤ N1) :
    |((Brockian.Equidistribution.configCount N q g a : ℝ) / H.mainTerm N)
        - H.C / ((q : ℝ) - 2)| ≤ (1 / 3 : ℝ) :=
  perConfig_normalized_deviation_le_epsilon H B ha hN0 hN1

/-- Total-count version of the finite `1/3` error budget. The right side is
`(q - 2)/3`, not an equidistribution theorem. -/
theorem totalConfig_normalized_deviation_le_one_third_scaled
    {q : ℕ} [NeZero q] {g N0 N1 : ℕ} (hq : 2 < q)
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    (B : FiniteRangeErrorBudget H N0 N1 (1 / 3 : ℝ))
    {N : ℕ} (hN0 : N0 ≤ N) (hN1 : N ≤ N1) :
    |((Brockian.Equidistribution.totalConfigCount N q g : ℝ) / H.mainTerm N) - H.C|
      ≤ ((q : ℝ) - 2) * (1 / 3 : ℝ) :=
  totalConfig_normalized_deviation_le_scaled_epsilon hq H B hN0 hN1

end Brockian.Equidistribution.DeviationBound
