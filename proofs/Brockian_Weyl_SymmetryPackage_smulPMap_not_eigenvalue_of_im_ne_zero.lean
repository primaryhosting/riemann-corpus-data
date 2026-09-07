/-
  Brockian/WeylSymmetryPackage.lean — New-Era reading-path package of the load-bearing
  `IsSymmetric` facts from `WeylOperator`.

  Purpose: a short, gallery-friendly re-export of the real-spectrum / injectivity /
  basic-inequality rung for symmetric partially-defined operators. Downstream modules
  and the New Era reading path can import this file instead of reaching into the full
  operator scaffolding.

  Built on (import only):
    * `Brockian/WeylOperator.lean` (`Brockian.Weyl.Operator`)
    * Mathlib

  ## What is packaged (all hole-free re-exports / thin corollaries)

    * `quadratic_form_im_zero`     — `⟪T v, v⟫` is real (`Im = 0`)
    * `eigenvalue_im_zero`         — eigenvalues of a symmetric `T` are real
    * `norm_sub_smul_ge`           — basic inequality `‖T v − z·v‖ ≥ |Im z|·‖v‖`
    * `injective_of_im_ne_zero`    — `T − z` injective on the domain when `Im z ≠ 0`
    * `not_eigenvalue_of_im_ne_zero` — nonreal `z` is never a point-spectrum value
    * `SymmetricRealSpectrum`      — flagship package structure (reading path)
    * Gate-0 non-vacuity on `smulPMap` under the package names

  ## Honest non-claims

  * Does **not** prove essential self-adjointness, `T̄ = T*`, or the Weyl criterion.
  * Does **not** claim real spectrum of the adjoint / closure beyond the eigenvalue
    statements already proved for the symmetric operator itself in `WeylOperator`.
  * No ESA assertions beyond the predicate definitions already in `WeylOperator`
    (this file does not re-export deficiency / ESA material).

  Verification (spec §2A): AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylOperator

namespace Brockian.Weyl.SymmetryPackage

open scoped InnerProductSpace
open Brockian.Weyl.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Real quadratic form -/

/-- **The quadratic form of a symmetric operator is real.** For any `v` in the
domain, `⟪T v, v⟫` has zero imaginary part. Re-export of
`IsSymmetric.inner_self_im` under a New-Era reading-path name. -/
theorem quadratic_form_im_zero {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) : (⟪T v, (v : H)⟫_ℂ).im = 0 :=
  hT.inner_self_im v

/-! ### Real eigenvalues -/

/-- **Eigenvalues of a symmetric operator are real.** If `T v = μ • v` for a
nonzero domain vector, then `μ.im = 0`. Re-export of
`IsSymmetric.im_eq_zero_of_apply_eq_smul`. -/
theorem eigenvalue_im_zero {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {v : T.domain} {μ : ℂ} (hv : (v : H) ≠ 0)
    (heig : T v = μ • (v : H)) : μ.im = 0 :=
  hT.im_eq_zero_of_apply_eq_smul hv heig

/-! ### Basic symmetric-operator inequality -/

/-- **Basic symmetric-operator inequality** `‖T v − z · v‖ ≥ |Im z| · ‖v‖`.
Re-export of `IsSymmetric.norm_sub_smul_ge` — the analytic heart of the real-
spectrum / injectivity story. -/
theorem norm_sub_smul_ge {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) (z : ℂ) : |z.im| * ‖(v : H)‖ ≤ ‖T v - z • (v : H)‖ :=
  hT.norm_sub_smul_ge v z

/-! ### Injectivity of `T − z` for nonreal `z` -/

/-- **`T − z` is injective on the domain when `Im z ≠ 0`.** If `T v = z • v`
then `v = 0`. Re-export of `IsSymmetric.eq_zero_of_apply_eq_smul`. -/
theorem injective_of_im_ne_zero {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {z : ℂ} (hz : z.im ≠ 0) {v : T.domain}
    (h : T v = z • (v : H)) : (v : H) = 0 :=
  hT.eq_zero_of_apply_eq_smul hz h

/-- **Nonreal scalars are never eigenvalues of a symmetric operator.** Contrapositive
form of injectivity: if `Im z ≠ 0` and `v ≠ 0`, then `T v ≠ z • v`. Thin corollary,
hole-free. -/
theorem not_eigenvalue_of_im_ne_zero {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {z : ℂ} (hz : z.im ≠ 0) {v : T.domain} (hv : (v : H) ≠ 0) :
    T v ≠ z • (v : H) := by
  intro h
  exact hv (injective_of_im_ne_zero hT hz h)

/-! ### Reading-path package -/

/-- Flagship package: real quadratic form + real eigenvalues + basic inequality +
injectivity at nonreal spectral parameters. No ESA / Weyl-criterion content. -/
structure SymmetricRealSpectrum where
  quadratic_form_real :
    ∀ {T : H →ₗ.[ℂ] H}, IsSymmetric T → ∀ v : T.domain, (⟪T v, (v : H)⟫_ℂ).im = 0
  eigenvalues_real :
    ∀ {T : H →ₗ.[ℂ] H}, IsSymmetric T → ∀ {v : T.domain} {μ : ℂ},
      (v : H) ≠ 0 → T v = μ • (v : H) → μ.im = 0
  basic_inequality :
    ∀ {T : H →ₗ.[ℂ] H}, IsSymmetric T → ∀ (v : T.domain) (z : ℂ),
      |z.im| * ‖(v : H)‖ ≤ ‖T v - z • (v : H)‖
  injective_nonreal :
    ∀ {T : H →ₗ.[ℂ] H}, IsSymmetric T → ∀ {z : ℂ}, z.im ≠ 0 →
      ∀ {v : T.domain}, T v = z • (v : H) → (v : H) = 0

/-- Instantiation of the package from the verified `IsSymmetric` facts. -/
noncomputable def symmetricRealSpectrum : SymmetricRealSpectrum (H := H) where
  quadratic_form_real := fun hT v => quadratic_form_im_zero hT v
  eigenvalues_real := fun hT _ _ hv heig => eigenvalue_im_zero hT hv heig
  basic_inequality := fun hT v z => norm_sub_smul_ge hT v z
  injective_nonreal := fun hT _ hz _ h => injective_of_im_ne_zero hT hz h

/-! ### Gate-0 non-vacuity (package names on the real-scalar witness) -/

/-- The real-scalar operator is symmetric (Gate-0 from `WeylOperator`). -/
theorem smulPMap_isSymmetric (c : ℝ) : IsSymmetric (smulPMap (H := H) c) :=
  Brockian.Weyl.Operator.smulPMap_isSymmetric c

/-- Package fact on the witness: quadratic form of `smulPMap c` is real. -/
theorem smulPMap_quadratic_form_im_zero (c : ℝ)
    (v : (smulPMap (H := H) c).domain) :
    (⟪smulPMap c v, (v : H)⟫_ℂ).im = 0 :=
  quadratic_form_im_zero (smulPMap_isSymmetric c) v

/-- Package fact on the witness: nonreal `z` is never an eigenvalue of `smulPMap c`. -/
theorem smulPMap_not_eigenvalue_of_im_ne_zero (c : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    {v : (smulPMap (H := H) c).domain} (hv : (v : H) ≠ 0) :
    smulPMap c v ≠ z • (v : H) :=
  not_eigenvalue_of_im_ne_zero (smulPMap_isSymmetric c) hz hv

end Brockian.Weyl.SymmetryPackage
