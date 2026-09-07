/-
  Brockian/CosTraceNorm.lean — Trace and Norm of the spectral generator
  `α_p = 2 cos(2π/p)` from the simple extension `ℚ(α_p)/ℚ`.

  Builds on `CosAlgebraicInteger` (integrality) and `GaloisWhyFive` (explicit
  minpolys / degrees for `p ∈ {3,5,7}`).  Uses Mathlib's standard dictionary:

    monic minpoly  `X^n + a_{n-1} X^{n-1} + ⋯ + a_0`
      ⇒  Trace_{ℚ(α)/ℚ}(α) = −a_{n-1} = −(minpoly).nextCoeff
      ⇒  Norm_{ℚ(α)/ℚ}(α)  = (−1)^n a_0

  ## What is proved

    * Re-exports: `isIntegral_spectralGen`, `isIntegral_two_cos_two_pi_div`
      (and their `ℚ`-base-change forms) from `CosAlgebraicInteger`.
    * General coefficient rules over `ℝ` for any integral `x`:
        `trace_adjoin_gen_eq_neg_nextCoeff`,
        `norm_adjoin_gen_eq_coeff_zero`.
    * Explicit minpolys:
        `minpoly_three`  (`X + 1`),
        `minpoly_five`   (`X² + X − 1 = Q5`),
        `minpoly_seven`  (`X³ + X² − 2X − 1 = P7`).
    * Coefficient packs + concrete Trace/Norm:
        p=3: degree 1, trace = −1, norm = −1
        p=5: degree 2, trace = −1, norm = −1
        p=7: degree 3, trace = −1, norm = 1

  ## What is NOT claimed

    * No numerology: values come only from monic minpoly coefficients.
    * No general formula for arbitrary primes beyond the coefficient rule
      (needs the general minpoly family for explicit `a_i`).
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNorm

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.CosAlgebraicInteger

/-! ### Re-export integrality from CosAlgebraicInteger -/

/-- `α_p = 2 cos(2π/p)` is an algebraic integer (over `ℤ`). -/
theorem isIntegral_spectralGen {p : ℕ} (hp : p.Prime) :
    IsIntegral ℤ (spectralGen p) :=
  CosAlgebraicInteger.isIntegral_spectralGen hp

/-- Same over `ℚ` (tower from `ℤ`). -/
theorem isIntegral_spectralGen_ℚ {p : ℕ} (hp : p.Prime) :
    IsIntegral ℚ (spectralGen p) :=
  CosAlgebraicInteger.isIntegral_spectralGen_ℚ hp

/-- `2 cos(2π/n)` is an algebraic integer for every positive `n`. -/
theorem isIntegral_two_cos_two_pi_div {n : ℕ} (hn : n ≠ 0) :
    IsIntegral ℤ (2 * Real.cos (2 * Real.pi / n)) :=
  CosAlgebraicInteger.isIntegral_two_cos_two_pi_div hn

/-- Same over `ℚ`. -/
theorem isIntegral_two_cos_two_pi_div_ℚ {n : ℕ} (hn : n ≠ 0) :
    IsIntegral ℚ (2 * Real.cos (2 * Real.pi / n)) :=
  CosAlgebraicInteger.isIntegral_two_cos_two_pi_div_ℚ hn

/-! ### General: Trace / Norm from monic minpoly coefficients -/

/-- **Trace rule.**  For any integral `x : ℝ`,
`Trace_{ℚ(x)/ℚ}(x) = −(minpoly ℚ x).nextCoeff`.
If the monic minpoly is `X^n + a_{n−1} X^{n−1} + ⋯ + a_0` with `n > 0`,
this is `−a_{n−1}`. -/
theorem trace_adjoin_gen_eq_neg_nextCoeff {x : ℝ} (hx : IsIntegral ℚ x) :
    Algebra.trace ℚ ℚ⟮x⟯ (AdjoinSimple.gen ℚ x) = -(minpoly ℚ x).nextCoeff :=
  trace_adjoinSimpleGen hx

/-- **Norm rule.**  For any integral `x : ℝ`,
`Norm_{ℚ(x)/ℚ}(x) = (−1)^{deg} · (minpoly ℚ x).coeff 0`.
If the monic minpoly is `X^n + a_{n−1} X^{n−1} + ⋯ + a_0`, this is `(−1)^n a_0`. -/
theorem norm_adjoin_gen_eq_coeff_zero {x : ℝ} (hx : IsIntegral ℚ x) :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ x) =
      (-1) ^ (minpoly ℚ x).natDegree * (minpoly ℚ x).coeff 0 := by
  -- Use the IntermediateField power basis (not Algebra.adjoin) to avoid ambiguity.
  set pb := IntermediateField.adjoin.powerBasis hx
  have hgen : pb.gen = AdjoinSimple.gen ℚ x :=
    IntermediateField.adjoin.powerBasis_gen hx
  -- Inline `minpoly_gen`: gen maps to `x` under the ambient algebraMap.
  have hmp : minpoly ℚ pb.gen = minpoly ℚ x := by
    rw [hgen, ← minpoly.algebraMap_eq (algebraMap ℚ⟮x⟯ ℝ).injective,
      AdjoinSimple.algebraMap_gen ℚ x]
  rw [← hgen]
  refine (PowerBasis.norm_gen_eq_coeff_zero_minpoly pb).trans ?_
  rw [IntermediateField.adjoin.powerBasis_dim hx]
  -- Avoid fragile `rw` matching on `minpoly pb.gen`; apply the equality by congruence.
  exact congrArg (fun p : ℚ[X] => (-1) ^ (minpoly ℚ x).natDegree * p.coeff 0) hmp

/-! ### Explicit minimal polynomials for p ∈ {3,5,7} -/

/-- **`minpoly ℚ α_3 = X + 1`.**  Since `α_3 = −1 ∈ ℚ`. -/
theorem minpoly_three : minpoly ℚ (spectralGen 3) = X + 1 := by
  have h : spectralGen 3 = algebraMap ℚ ℝ (-1) := by
    rw [spectralGen_three, map_neg, map_one]
  rw [h, minpoly.eq_X_sub_C]
  simp [sub_eq_add_neg]

/-- **`minpoly ℚ α_5 = X² + X − 1 = Q5`.**
Monic annihilator of matching degree is the minpoly. -/
theorem minpoly_five : minpoly ℚ (spectralGen 5) = Q5 := by
  have haev : (aeval (spectralGen 5)) Q5 = 0 := by
    rw [spectralGen_five]
    have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    unfold Q5
    simp only [map_sub, map_add, map_pow, aeval_X, map_one]
    linear_combination hsq
  have hint : IsIntegral ℚ (spectralGen 5) := ⟨Q5, Q5_monic, haev⟩
  have hdvd : minpoly ℚ (spectralGen 5) ∣ Q5 := minpoly.dvd ℚ _ haev
  -- `associated_of_dvd_of_natDegree_le` wants `q.natDegree ≤ p.natDegree`
  -- for `p ∣ q`, i.e. `Q5.natDegree ≤ minpoly.natDegree`.
  have hdeg : Q5.natDegree = (minpoly ℚ (spectralGen 5)).natDegree := by
    rw [degree_five, Q5_natDegree]
  -- `associated_of_dvd` + monic equality gives `minpoly = Q5` directly.
  exact eq_of_monic_of_associated (minpoly.monic hint) Q5_monic
    (associated_of_dvd_of_natDegree_le hdvd Q5_monic.ne_zero (le_of_eq hdeg))

/-- **`minpoly ℚ α_7 = X³ + X² − 2X − 1 = P7`.**
Irreducible monic annihilator is the minpoly. -/
theorem minpoly_seven : minpoly ℚ (spectralGen 7) = P7 :=
  (minpoly.eq_of_irreducible_of_monic P7_irreducible aeval_spectralGen_seven P7_monic).symm

/-! ### Coefficient packs (nextCoeff = a_{n−1}, coeff 0 = a_0) -/

theorem nextCoeff_minpoly_three : (minpoly ℚ (spectralGen 3)).nextCoeff = 1 := by
  rw [minpoly_three, ← C_1, nextCoeff_X_add_C]

theorem coeff_zero_minpoly_three : (minpoly ℚ (spectralGen 3)).coeff 0 = 1 := by
  rw [minpoly_three]
  simp [coeff_add, coeff_X, coeff_one]

theorem nextCoeff_minpoly_five : (minpoly ℚ (spectralGen 5)).nextCoeff = 1 := by
  rw [minpoly_five, nextCoeff_of_natDegree_pos (by rw [Q5_natDegree]; norm_num), Q5_natDegree]
  unfold Q5
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_X, coeff_one]

theorem coeff_zero_minpoly_five : (minpoly ℚ (spectralGen 5)).coeff 0 = -1 := by
  rw [minpoly_five]
  unfold Q5
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_X, coeff_one]

theorem nextCoeff_minpoly_seven : (minpoly ℚ (spectralGen 7)).nextCoeff = 1 := by
  rw [minpoly_seven, nextCoeff_of_natDegree_pos (by rw [P7_natDegree]; norm_num), P7_natDegree]
  unfold P7
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_X, coeff_one, coeff_mul]

theorem coeff_zero_minpoly_seven : (minpoly ℚ (spectralGen 7)).coeff 0 = -1 := by
  rw [minpoly_seven]
  unfold P7
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_X, coeff_one, coeff_mul]

/-! ### Trace / Norm for p = 3, 5, 7 -/

/-- Integrality of `α_3` over `ℚ` (degree-1 rational case). -/
theorem isIntegral_spectralGen_three_ℚ : IsIntegral ℚ (spectralGen 3) :=
  isIntegral_spectralGen_ℚ (by decide : Nat.Prime 3)

/-- Integrality of `α_5` over `ℚ`. -/
theorem isIntegral_spectralGen_five_ℚ : IsIntegral ℚ (spectralGen 5) :=
  isIntegral_spectralGen_ℚ (by decide : Nat.Prime 5)

/-- Integrality of `α_7` over `ℚ`. -/
theorem isIntegral_spectralGen_seven_ℚ : IsIntegral ℚ (spectralGen 7) :=
  isIntegral_spectralGen_ℚ (by decide : Nat.Prime 7)

/-- **p = 3:** `Trace_{ℚ(α_3)/ℚ}(α_3) = −1`. -/
theorem trace_spectralGen_three :
    Algebra.trace ℚ ℚ⟮spectralGen 3⟯ (AdjoinSimple.gen ℚ (spectralGen 3)) = -1 := by
  rw [trace_adjoin_gen_eq_neg_nextCoeff isIntegral_spectralGen_three_ℚ,
    nextCoeff_minpoly_three]

/-- **p = 3:** `Norm_{ℚ(α_3)/ℚ}(α_3) = −1`. -/
theorem norm_spectralGen_three :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 3)) = -1 := by
  rw [norm_adjoin_gen_eq_coeff_zero isIntegral_spectralGen_three_ℚ,
    degree_three, coeff_zero_minpoly_three]
  norm_num

/-- **p = 5:** `Trace_{ℚ(α_5)/ℚ}(α_5) = −1` (from `a_1 = 1` in `X² + X − 1`). -/
theorem trace_spectralGen_five :
    Algebra.trace ℚ ℚ⟮spectralGen 5⟯ (AdjoinSimple.gen ℚ (spectralGen 5)) = -1 := by
  rw [trace_adjoin_gen_eq_neg_nextCoeff isIntegral_spectralGen_five_ℚ,
    nextCoeff_minpoly_five]

/-- **p = 5:** `Norm_{ℚ(α_5)/ℚ}(α_5) = −1` (from `(−1)² · (−1)`). -/
theorem norm_spectralGen_five :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 5)) = -1 := by
  rw [norm_adjoin_gen_eq_coeff_zero isIntegral_spectralGen_five_ℚ,
    degree_five, coeff_zero_minpoly_five]
  norm_num

/-- **p = 7:** `Trace_{ℚ(α_7)/ℚ}(α_7) = −1` (from `a_2 = 1` in `X³ + X² − 2X − 1`). -/
theorem trace_spectralGen_seven :
    Algebra.trace ℚ ℚ⟮spectralGen 7⟯ (AdjoinSimple.gen ℚ (spectralGen 7)) = -1 := by
  rw [trace_adjoin_gen_eq_neg_nextCoeff isIntegral_spectralGen_seven_ℚ,
    nextCoeff_minpoly_seven]

/-- **p = 7:** `Norm_{ℚ(α_7)/ℚ}(α_7) = 1` (from `(−1)³ · (−1) = 1`). -/
theorem norm_spectralGen_seven :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 7)) = 1 := by
  rw [norm_adjoin_gen_eq_coeff_zero isIntegral_spectralGen_seven_ℚ,
    degree_seven, coeff_zero_minpoly_seven]
  norm_num

/-- Combined pack: degrees + traces + norms for `p ∈ {3,5,7}`. -/
theorem trace_norm_pack :
    (Algebra.trace ℚ ℚ⟮spectralGen 3⟯ (AdjoinSimple.gen ℚ (spectralGen 3)) = -1 ∧
      Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 3)) = -1) ∧
    (Algebra.trace ℚ ℚ⟮spectralGen 5⟯ (AdjoinSimple.gen ℚ (spectralGen 5)) = -1 ∧
      Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 5)) = -1) ∧
    (Algebra.trace ℚ ℚ⟮spectralGen 7⟯ (AdjoinSimple.gen ℚ (spectralGen 7)) = -1 ∧
      Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 7)) = 1) :=
  ⟨⟨trace_spectralGen_three, norm_spectralGen_three⟩,
    ⟨trace_spectralGen_five, norm_spectralGen_five⟩,
    ⟨trace_spectralGen_seven, norm_spectralGen_seven⟩⟩

end Brockian.CosTraceNorm
