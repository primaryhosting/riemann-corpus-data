import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Arithmetic fibre perturbation and Feshbach–Schur transfer

This file develops, over a real or complex (`RCLike`) inner product space,
two packages of operator-theoretic results.

## Part A — gap stability

For a self-adjoint operator `L` with a protected kernel vector `u` (`L u = 0`) and a spectral
gap `g > 0` on `uᗮ`, and a self-adjoint perturbation `E` with `E u = 0` and `‖E‖ ≤ eps < g`:

* `Brockian.ArithmeticFiber.orthogonal_invariant_of_annihilates`: `uᗮ` is invariant.
* `Brockian.ArithmeticFiber.perturbation_stability`: the quadratic form of `L + E` on `uᗮ`
  is bounded below by `(g - eps) * ‖x‖ ^ 2`.
* `Brockian.ArithmeticFiber.eigenvalue_displacement`: every eigenvalue of `L + E` with
  eigenvector orthogonal to `u` is at least `g - eps`; the kernel stays protected.

## Part B — exact Feshbach–Schur reduction

For an orthogonal decomposition `H = U ⊕ W` (modelled by `WithLp 2 (U × W)`) and a block
operator `M = [[A, B*], [B, D]]` (`blockOp`, self-adjoint by `isSelfAdjoint_blockOp`), with `z`
a scalar such that `D - z` is invertible with inverse `R`, the Feshbach map is
`feshbachOp A B* B z R = A - z - B* R B`.

* `mem_ker_blockOp_iff_feshbach`: the exact Feshbach–Schur equations.
* `feshbach_schur_kernel_equiv`: `ker (M - z) ≃ₗ ker (F z)`, with explicit forward map
  `x ↦ x₁` and inverse map `a ↦ (a, -(D - z)⁻¹ B a)`.
* `norm_sub_smul_lower_bound_infDist`, `isUnit_sub_smul_of_infDist`: for self-adjoint `D` in
  finite dimension, `dist z (spectrum D) ≥ delta > 0` gives invertibility of `D - z` together
  with the resolvent bound `‖(D - z)⁻¹‖ ≤ 1 / delta`.
* `feshbach_schur_enclosure`: `‖B* (D - z)⁻¹ B‖ ≤ ‖B‖ ^ 2 / delta`.
* `spectral_enclosure_of_lower_bound`, `feshbach_schur_spectral_enclosure`,
  `spectrum_blockOp_subset`: the resulting spectral enclosure for `M`.
* `fibreResolvent`, `effectiveBaseOp`, `cleanFibre_kernel_equiv`, `cleanFibre_enclosure`,
  `cleanFibre_spectral_enclosure`: the specialization to a clean blow-up, where the fibre block
  is the identity `D = 1` on the zero-sum fibre space. There the effective base operator is
  `A - (1 - z)⁻¹ B* B` and the enclosure reads `‖B* (1 - z)⁻¹ B‖ ≤ ‖B‖ ^ 2 / ‖z - 1‖`.

All results are stated over a real or complex scalar field `𝕜` (`RCLike`).
-/

open scoped InnerProductSpace
open RCLike

namespace Brockian.ArithmeticFiber

section PartA

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A self-adjoint operator annihilating `u` maps everything into `uᗮ`; in particular the
orthogonal complement of the protected vector `u` is an invariant subspace. -/
theorem mapsTo_orthogonal_of_annihilates {L : H →L[𝕜] H} (hL : IsSelfAdjoint L) {u : H}
    (hu : L u = 0) (x : H) : L x ∈ (𝕜 ∙ u)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hL) u x
  simpa [hu] using h.symm

/-- The orthogonal complement `uᗮ` of a vector annihilated by a self-adjoint operator `L` is
invariant under `L`. -/
theorem orthogonal_invariant_of_annihilates {L : H →L[𝕜] H} (hL : IsSelfAdjoint L) {u : H}
    (hu : L u = 0) :
    Submodule.map (L : H →ₗ[𝕜] H) ((𝕜 ∙ u)ᗮ : Submodule 𝕜 H) ≤ ((𝕜 ∙ u)ᗮ : Submodule 𝕜 H) := by
  rintro _ ⟨x, -, rfl⟩
  exact mapsTo_orthogonal_of_annihilates hL hu x

/-- `uᗮ` is invariant under the perturbed operator `L + E` as well. -/
theorem orthogonal_invariant_add {L E : H →L[𝕜] H} (hL : IsSelfAdjoint L) (hE : IsSelfAdjoint E)
    {u : H} (hLu : L u = 0) (hEu : E u = 0) :
    Submodule.map ((L + E : H →L[𝕜] H) : H →ₗ[𝕜] H) ((𝕜 ∙ u)ᗮ : Submodule 𝕜 H)
      ≤ ((𝕜 ∙ u)ᗮ : Submodule 𝕜 H) := by
  rintro _ ⟨x, -, rfl⟩
  refine mapsTo_orthogonal_of_annihilates (hL.add hE) ?_ x
  simp [hLu, hEu]

omit [CompleteSpace H] in
/-- Elementary bound for the real part of the quadratic form of an operator. -/
theorem abs_re_inner_le (E : H →L[𝕜] H) (x : H) : |re ⟪x, E x⟫_𝕜| ≤ ‖E‖ * ‖x‖ ^ 2 := by
  have h1 : |re ⟪x, E x⟫_𝕜| ≤ ‖⟪x, E x⟫_𝕜‖ := abs_re_le_norm _
  have h2 : ‖⟪x, E x⟫_𝕜‖ ≤ ‖x‖ * ‖E x‖ := norm_inner_le_norm _ _
  have h3 : ‖E x‖ ≤ ‖E‖ * ‖x‖ := E.le_opNorm x
  nlinarith [norm_nonneg x, norm_nonneg (E x), norm_nonneg E]

omit [CompleteSpace H] in
/-- A Weyl-type estimate: the Rayleigh quotient moves by at most `‖E‖` under the
perturbation `E`. -/
theorem rayleigh_shift_bound (L E : H →L[𝕜] H) {eps : ℝ} (hE : ‖E‖ ≤ eps) (x : H) :
    |re ⟪x, (L + E) x⟫_𝕜 - re ⟪x, L x⟫_𝕜| ≤ eps * ‖x‖ ^ 2 := by
  have hx : re ⟪x, (L + E) x⟫_𝕜 - re ⟪x, L x⟫_𝕜 = re ⟪x, E x⟫_𝕜 := by
    simp [inner_add_right, map_add]
  rw [hx]
  refine (abs_re_inner_le E x).trans ?_
  have := sq_nonneg ‖x‖
  nlinarith

omit [CompleteSpace H] in
/-- **Part A.2 — perturbation stability of the gap.** If the quadratic form of `L` is bounded
below by `g * ‖x‖ ^ 2` on `uᗮ` and `‖E‖ ≤ eps`, then the quadratic form of `L + E` is bounded
below by `(g - eps) * ‖x‖ ^ 2` on `uᗮ`. -/
theorem perturbation_stability {L E : H →L[𝕜] H} {u : H} {g eps : ℝ}
    (hgap : ∀ y ∈ (𝕜 ∙ u)ᗮ, g * ‖y‖ ^ 2 ≤ re ⟪y, L y⟫_𝕜) (hE : ‖E‖ ≤ eps)
    {x : H} (hx : x ∈ (𝕜 ∙ u)ᗮ) :
    (g - eps) * ‖x‖ ^ 2 ≤ re ⟪x, (L + E) x⟫_𝕜 := by
  have h1 := hgap x hx
  have h2 := abs_re_inner_le E x
  have h3 : -(eps * ‖x‖ ^ 2) ≤ re ⟪x, E x⟫_𝕜 := by
    have h4 : ‖E‖ * ‖x‖ ^ 2 ≤ eps * ‖x‖ ^ 2 := by
      have := sq_nonneg ‖x‖
      nlinarith
    have h5 := abs_le.mp h2
    linarith [h5.1]
  have h6 : re ⟪x, (L + E) x⟫_𝕜 = re ⟪x, L x⟫_𝕜 + re ⟪x, E x⟫_𝕜 := by
    simp [inner_add_right, map_add]
  rw [h6]
  nlinarith

omit [CompleteSpace H] in
/-- The kernel direction is protected: `u` stays in the kernel of the perturbed operator. -/
theorem protected_kernel {L E : H →L[𝕜] H} {u : H} (hLu : L u = 0) (hEu : E u = 0) :
    (L + E) u = 0 := by simp [hLu, hEu]

omit [CompleteSpace H] in
/-- **Part A.3 — eigenvalue displacement.** Every eigenvalue of `L + E` whose eigenvector is
orthogonal to the protected vector `u` has real part at least `g - eps`; combined with
`protected_kernel` this says the spectral gap of `L + E` above its protected kernel is at
least `g - eps`. -/
theorem eigenvalue_displacement {L E : H →L[𝕜] H} {u : H} {g eps : ℝ}
    (hgap : ∀ y ∈ (𝕜 ∙ u)ᗮ, g * ‖y‖ ^ 2 ≤ re ⟪y, L y⟫_𝕜) (hE : ‖E‖ ≤ eps)
    {x : H} (hx : x ∈ (𝕜 ∙ u)ᗮ) (hx0 : x ≠ 0) {mu : 𝕜} (heig : (L + E) x = mu • x) :
    g - eps ≤ re mu := by
  have hxpos : 0 < ‖x‖ ^ 2 := by positivity
  have hform : re ⟪x, (L + E) x⟫_𝕜 = re mu * ‖x‖ ^ 2 := by
    rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.mul_re]
    simp
  have h := perturbation_stability hgap hE hx
  rw [hform] at h
  exact le_of_mul_le_mul_right (by linarith) hxpos

/-- Non-vacuity witness for Part A: for every vector `u`, the operator `L = 1 - P_u`, where `P_u`
is the orthogonal projection onto `𝕜 ∙ u`, is self-adjoint, annihilates `u`, and has spectral
gap `g = 1` on `uᗮ`; so the hypotheses of `perturbation_stability` are satisfiable. -/
theorem projectionComplement_gap_model (u : H) :
    IsSelfAdjoint ((1 : H →L[𝕜] H) - (𝕜 ∙ u).starProjection) ∧
      ((1 : H →L[𝕜] H) - (𝕜 ∙ u).starProjection) u = 0 ∧
      ∀ x ∈ (𝕜 ∙ u)ᗮ,
        (1 : ℝ) * ‖x‖ ^ 2 ≤ re ⟪x, ((1 : H →L[𝕜] H) - (𝕜 ∙ u).starProjection) x⟫_𝕜 := by
  refine ⟨IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_starProjection (𝕜 ∙ u)), ?_, ?_⟩
  · have h : (𝕜 ∙ u).starProjection u = u :=
      Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self u)
    simp [h]
  · intro x hx
    have h0 : (𝕜 ∙ u).starProjection x = 0 := (Submodule.starProjection_apply_eq_zero_iff _).mpr hx
    simp [h0, inner_self_eq_norm_sq_to_K]

end PartA

section SpectralTools

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

/-- An eigenvalue of a continuous linear operator belongs to its spectrum. -/
theorem mem_spectrum_of_eigen {T : X →L[𝕜] X} {mu : 𝕜} {v : X} (hv : v ≠ 0)
    (h : T v = mu • v) : mu ∈ spectrum 𝕜 T := by
  rw [spectrum.mem_iff]
  rintro ⟨V, hV⟩
  have hVv : (↑V : X →L[𝕜] X) v = 0 := by
    rw [hV]; simp [Algebra.algebraMap_eq_smul_one, h]
  have h2 : (↑V⁻¹ * ↑V : X →L[𝕜] X) v = v := by rw [V.inv_mul]; rfl
  rw [ContinuousLinearMap.mul_apply, hVv, map_zero] at h2
  exact hv h2.symm

/-- On a finite dimensional space, an injective continuous linear operator is invertible. -/
theorem isUnit_of_injective [FiniteDimensional 𝕜 X] {T : X →L[𝕜] X}
    (h : Function.Injective T) : IsUnit T := by
  have hb : Function.Bijective (T : X →ₗ[𝕜] X) :=
    ⟨h, (LinearMap.injective_iff_surjective (f := (T : X →ₗ[𝕜] X))).mp h⟩
  let e : X ≃ₗ[𝕜] X := LinearEquiv.ofBijective (T : X →ₗ[𝕜] X) hb
  refine ⟨⟨T, LinearMap.toContinuousLinearMap (e.symm : X →ₗ[𝕜] X), ?_, ?_⟩, rfl⟩
  · ext x
    show T (e.symm x) = x
    exact e.apply_symm_apply x
  · ext x
    show e.symm (T x) = x
    exact e.symm_apply_apply x

/-- An operator bounded below by a positive constant does not have `0` in its spectrum;
more precisely, it is invertible (in finite dimension). -/
theorem isUnit_of_lower_bound [FiniteDimensional 𝕜 X] {T : X →L[𝕜] X} {c : ℝ} (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ≤ ‖T x‖) : IsUnit T := by
  refine isUnit_of_injective ?_
  intro x y hxy
  have h : c * ‖x - y‖ ≤ ‖T (x - y)‖ := hT _
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have h2 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
  have hx : x - y = 0 := norm_eq_zero.mp (le_antisymm h2 (norm_nonneg _))
  exact sub_eq_zero.mp hx

/-- **Quantitative resolvent lower bound.** For a self-adjoint operator `D` on a finite
dimensional space, if every spectral point of `D` is at distance at least `delta` from `z`, then
`D - z` is bounded below by `delta`. -/
theorem norm_sub_smul_lower_bound [FiniteDimensional 𝕜 X] [CompleteSpace X] {D : X →L[𝕜] X}
    (hD : IsSelfAdjoint D) {z : 𝕜} {delta : ℝ}
    (hdelta : ∀ mu ∈ spectrum 𝕜 D, delta ≤ ‖mu - z‖) (w : X) :
    delta * ‖w‖ ≤ ‖(D - z • 1) w‖ := by
  rcases le_or_gt delta 0 with hd | hd
  · nlinarith [norm_nonneg w, norm_nonneg ((D - z • (1 : X →L[𝕜] X)) w)]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hD
  set n := Module.finrank 𝕜 X with hn
  set b := hsym.eigenvectorBasis (n := n) rfl with hb
  set lam := hsym.eigenvalues (n := n) rfl with hlam
  have hspec : ∀ i, ((lam i : ℝ) : 𝕜) ∈ spectrum 𝕜 D := by
    intro i
    refine mem_spectrum_of_eigen (v := b i) ?_ ?_
    · intro h0
      have h1 := b.orthonormal.1 i
      rw [h0] at h1; simp at h1
    · exact hsym.apply_eigenvectorBasis rfl i
  have key : ∀ i, ⟪b i, (D - z • (1 : X →L[𝕜] X)) w⟫_𝕜
      = (((lam i : ℝ) : 𝕜) - z) * ⟪b i, w⟫_𝕜 := by
    intro i
    have h1 : ⟪b i, D w⟫_𝕜 = ((lam i : ℝ) : 𝕜) * ⟪b i, w⟫_𝕜 := by
      have h0 : ⟪(D : X →ₗ[𝕜] X) (b i), w⟫_𝕜 = ⟪b i, (D : X →ₗ[𝕜] X) w⟫_𝕜 := hsym (b i) w
      rw [hsym.apply_eigenvectorBasis rfl i, inner_smul_left] at h0
      simpa using h0.symm
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right, h1]
    ring
  have hsum : ‖(D - z • (1 : X →L[𝕜] X)) w‖ ^ 2
      = ∑ i, ‖(((lam i : ℝ) : 𝕜) - z) * ⟪b i, w⟫_𝕜‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right]
    exact Finset.sum_congr rfl fun i _ => by rw [key i]
  have hlow : delta ^ 2 * ‖w‖ ^ 2 ≤ ‖(D - z • (1 : X →L[𝕜] X)) w‖ ^ 2 := by
    rw [hsum, ← b.sum_sq_norm_inner_right w, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_pow]
    have h1 := hdelta _ (hspec i)
    have h2 : delta ^ 2 ≤ ‖((lam i : ℝ) : 𝕜) - z‖ ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖⟪b i, w⟫_𝕜‖, norm_nonneg ⟪b i, w⟫_𝕜]
  nlinarith [norm_nonneg w, norm_nonneg ((D - z • (1 : X →L[𝕜] X)) w), hd.le]

/-- The same bound, phrased with the distance from `z` to the spectrum of `D`. -/
theorem norm_sub_smul_lower_bound_infDist [FiniteDimensional 𝕜 X] [CompleteSpace X]
    {D : X →L[𝕜] X} (hD : IsSelfAdjoint D) {z : 𝕜} {delta : ℝ}
    (hdelta : delta ≤ Metric.infDist z (spectrum 𝕜 D)) (w : X) :
    delta * ‖w‖ ≤ ‖(D - z • 1) w‖ := by
  refine norm_sub_smul_lower_bound hD (fun mu hmu => ?_) w
  have h := Metric.infDist_le_dist_of_mem (x := z) hmu
  rw [dist_eq_norm] at h
  rw [← norm_sub_rev]
  linarith

/-- If `z` is at positive distance from the spectrum of the self-adjoint operator `D`,
then `D - z` is invertible. -/
theorem isUnit_sub_smul_of_infDist [FiniteDimensional 𝕜 X] [CompleteSpace X]
    {D : X →L[𝕜] X} (hD : IsSelfAdjoint D) {z : 𝕜} {delta : ℝ} (hdelta : 0 < delta)
    (hz : delta ≤ Metric.infDist z (spectrum 𝕜 D)) : IsUnit (D - z • 1) :=
  isUnit_of_lower_bound hdelta (norm_sub_smul_lower_bound_infDist hD hz)

/-- Norm bound for a right inverse of an operator that is bounded below. -/
theorem norm_le_of_lower_bound_of_rightInverse {T R : X →L[𝕜] X} {delta : ℝ} (hdelta : 0 < delta)
    (hT : ∀ x, delta * ‖x‖ ≤ ‖T x‖) (hR : T ∘L R = 1) : ‖R‖ ≤ 1 / delta := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have h1 : delta * ‖R v‖ ≤ ‖T (R v)‖ := hT _
  have h2 : T (R v) = v := by simpa using ContinuousLinearMap.ext_iff.mp hR v
  rw [h2] at h1
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hdelta]
  linarith

end SpectralTools

section PartB

variable {𝕜 U W : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

open ContinuousLinearMap in
/-- The block operator `[[A, C], [B, D]]` acting on the orthogonal direct sum
`H = U ⊕ W`, modelled as `WithLp 2 (U × W)`. -/
noncomputable def blockOp (A : U →L[𝕜] U) (C : W →L[𝕜] U) (B : U →L[𝕜] W) (D : W →L[𝕜] W) :
    WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 U W).symm : (U × W) →L[𝕜] WithLp 2 (U × W)) ∘L
    ((A ∘L fst 𝕜 U W + C ∘L snd 𝕜 U W).prod (B ∘L fst 𝕜 U W + D ∘L snd 𝕜 U W)) ∘L
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 U W) : WithLp 2 (U × W) →L[𝕜] (U × W))

@[simp] theorem blockOp_ofLp (A : U →L[𝕜] U) (C : W →L[𝕜] U) (B : U →L[𝕜] W) (D : W →L[𝕜] W)
    (x : WithLp 2 (U × W)) :
    WithLp.ofLp (blockOp A C B D x)
      = (A (WithLp.ofLp x).1 + C (WithLp.ofLp x).2, B (WithLp.ofLp x).1 + D (WithLp.ofLp x).2) :=
  rfl

/-- The Feshbach–Schur map `F z = A - z - C R B`, where `R` is meant to be `(D - z)⁻¹`. -/
noncomputable def feshbachOp (A : U →L[𝕜] U) (C : W →L[𝕜] U) (B : U →L[𝕜] W) (z : 𝕜)
    (R : W →L[𝕜] W) : U →L[𝕜] U := A - z • 1 - C ∘L (R ∘L B)

@[simp] theorem feshbachOp_apply (A : U →L[𝕜] U) (C : W →L[𝕜] U) (B : U →L[𝕜] W) (z : 𝕜)
    (R : W →L[𝕜] W) (a : U) : feshbachOp A C B z R a = A a - z • a - C (R (B a)) := rfl

section SelfAdjoint

variable [CompleteSpace U] [CompleteSpace W]

theorem inner_left_of_isSelfAdjoint {A : U →L[𝕜] U} (hA : IsSelfAdjoint A) (p q : U) :
    ⟪A p, q⟫_𝕜 = ⟪p, A q⟫_𝕜 := by
  have h := ContinuousLinearMap.adjoint_inner_left A q p
  rwa [hA.adjoint_eq] at h

open ContinuousLinearMap in
/-- With `C = B*` and self-adjoint diagonal blocks, the block operator is self-adjoint. -/
theorem isSelfAdjoint_blockOp {A : U →L[𝕜] U} {D : W →L[𝕜] W} (B : U →L[𝕜] W)
    (hA : IsSelfAdjoint A) (hD : IsSelfAdjoint D) :
    IsSelfAdjoint (blockOp A (adjoint B) B D) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, WithLp.prod_inner_apply, blockOp_ofLp,
    inner_add_left, inner_add_right]
  rw [inner_left_of_isSelfAdjoint hA, inner_left_of_isSelfAdjoint hD,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  ring

end SelfAdjoint

theorem mem_ker_blockOp_iff (A : U →L[𝕜] U) (C : W →L[𝕜] U) (B : U →L[𝕜] W) (D : W →L[𝕜] W)
    (z : 𝕜) (x : WithLp 2 (U × W)) :
    x ∈ LinearMap.ker ((blockOp A C B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) :
        WithLp 2 (U × W) →ₗ[𝕜] WithLp 2 (U × W)) ↔
      (A (WithLp.ofLp x).1 + C (WithLp.ofLp x).2 - z • (WithLp.ofLp x).1 = 0 ∧
        B (WithLp.ofLp x).1 + D (WithLp.ofLp x).2 - z • (WithLp.ofLp x).2 = 0) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h0 : WithLp.ofLp ((blockOp A C B D - z • 1) x) = 0 := by
      rw [show ((blockOp A C B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) x) = 0 from h]
      rfl
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply] at h0
    exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
  · rintro ⟨h1, h2⟩
    refine WithLp.ofLp_injective 2 ?_
    have h3 : WithLp.ofLp (blockOp A C B D x - z • x) =
        (A (WithLp.ofLp x).1 + C (WithLp.ofLp x).2 - z • (WithLp.ofLp x).1,
          B (WithLp.ofLp x).1 + D (WithLp.ofLp x).2 - z • (WithLp.ofLp x).2) := rfl
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
    rw [h3, h1, h2]
    rfl

variable {A : U →L[𝕜] U} {C : W →L[𝕜] U} {B : U →L[𝕜] W} {D : W →L[𝕜] W} {z : 𝕜} {R : W →L[𝕜] W}

/-- **The exact Feshbach–Schur equations.** A vector `x = (a, w)` lies in the kernel of `M - z`
if and only if `w = -(D - z)⁻¹ B a` and `a` lies in the kernel of the Feshbach map. -/
theorem mem_ker_blockOp_iff_feshbach (hR₁ : (D - z • 1) ∘L R = 1) (hR₂ : R ∘L (D - z • 1) = 1)
    (x : WithLp 2 (U × W)) :
    x ∈ LinearMap.ker ((blockOp A C B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) :
        WithLp 2 (U × W) →ₗ[𝕜] WithLp 2 (U × W)) ↔
      ((WithLp.ofLp x).2 = -(R (B (WithLp.ofLp x).1)) ∧
        feshbachOp A C B z R (WithLp.ofLp x).1 = 0) := by
  have e₁ : ∀ w : W, D (R w) - z • R w = w := by
    intro w; simpa using ContinuousLinearMap.ext_iff.mp hR₁ w
  have e₂ : ∀ w : W, R (D w - z • w) = w := by
    intro w; simpa using ContinuousLinearMap.ext_iff.mp hR₂ w
  rw [mem_ker_blockOp_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hx2 : (WithLp.ofLp x).2 = -(R (B (WithLp.ofLp x).1)) := by
      have h3 : D (WithLp.ofLp x).2 - z • (WithLp.ofLp x).2 = -(B (WithLp.ofLp x).1) := by
        rw [eq_neg_iff_add_eq_zero]
        linear_combination (norm := abel_nf) h2
      have h4 := congrArg R h3
      rw [e₂, map_neg] at h4
      exact h4
    refine ⟨hx2, ?_⟩
    rw [hx2, map_neg] at h1
    rw [feshbachOp_apply]
    linear_combination (norm := abel_nf) h1
  · rintro ⟨hx2, hF⟩
    rw [feshbachOp_apply] at hF
    refine ⟨?_, ?_⟩
    · rw [hx2, map_neg]
      linear_combination (norm := abel_nf) hF
    · rw [hx2, map_neg, smul_neg, sub_neg_eq_add]
      have h := e₁ (B (WithLp.ofLp x).1)
      abel_nf
      abel_nf at h
      linear_combination (norm := abel_nf) -h

/-- **Part B.4 — the Feshbach–Schur kernel isomorphism.** The kernel of `M - z` is linearly
isomorphic to the kernel of the Feshbach map `F z = A - z - C (D - z)⁻¹ B`; the forward map is
the projection onto the `U` component and the inverse map is `a ↦ (a, -(D - z)⁻¹ B a)`. -/
noncomputable def feshbach_schur_kernel_equiv (hR₁ : (D - z • 1) ∘L R = 1)
    (hR₂ : R ∘L (D - z • 1) = 1) :
    LinearMap.ker ((blockOp A C B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) :
        WithLp 2 (U × W) →ₗ[𝕜] WithLp 2 (U × W)) ≃ₗ[𝕜]
      LinearMap.ker ((feshbachOp A C B z R : U →L[𝕜] U) : U →ₗ[𝕜] U) where
  toFun x := ⟨(WithLp.ofLp (x : WithLp 2 (U × W))).1,
    ((mem_ker_blockOp_iff_feshbach hR₁ hR₂ _).mp x.2).2⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun a := ⟨WithLp.toLp 2 ((a : U), -(R (B (a : U)))),
    (mem_ker_blockOp_iff_feshbach hR₁ hR₂ _).mpr ⟨rfl, a.2⟩⟩
  left_inv x := by
    refine Subtype.ext (WithLp.ofLp_injective 2 ?_)
    have h := ((mem_ker_blockOp_iff_feshbach hR₁ hR₂ _).mp x.2).1
    exact Prod.ext rfl h.symm
  right_inv a := rfl

@[simp] theorem feshbach_schur_kernel_equiv_apply (hR₁ : (D - z • 1) ∘L R = 1)
    (hR₂ : R ∘L (D - z • 1) = 1)
    (x : LinearMap.ker ((blockOp A C B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) :
        WithLp 2 (U × W) →ₗ[𝕜] WithLp 2 (U × W))) :
    (feshbach_schur_kernel_equiv hR₁ hR₂ x : U) = (WithLp.ofLp (x : WithLp 2 (U × W))).1 := rfl

@[simp] theorem feshbach_schur_kernel_equiv_symm_apply (hR₁ : (D - z • 1) ∘L R = 1)
    (hR₂ : R ∘L (D - z • 1) = 1)
    (a : LinearMap.ker ((feshbachOp A C B z R : U →L[𝕜] U) : U →ₗ[𝕜] U)) :
    ((feshbach_schur_kernel_equiv hR₁ hR₂).symm a : WithLp 2 (U × W))
      = WithLp.toLp 2 ((a : U), -(R (B (a : U)))) := rfl

section Enclosure

variable [CompleteSpace U] [CompleteSpace W] [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 W]

omit [FiniteDimensional 𝕜 U] in
open ContinuousLinearMap in
/-- **Part B.5 — norm bound on the Feshbach correction.** If `z` is at distance at least
`delta > 0` from the spectrum of the self-adjoint operator `D` and `R` is a right inverse of
`D - z`, then `‖B* R B‖ ≤ ‖B‖ ^ 2 / delta`. -/
theorem feshbach_schur_enclosure {delta : ℝ} (hD : IsSelfAdjoint D) (hdelta : 0 < delta)
    (hz : delta ≤ Metric.infDist z (spectrum 𝕜 D)) (hR₁ : (D - z • 1) ∘L R = 1) :
    ‖(adjoint B) ∘L (R ∘L B)‖ ≤ ‖B‖ ^ 2 / delta := by
  have hR : ‖R‖ ≤ 1 / delta :=
    norm_le_of_lower_bound_of_rightInverse hdelta (norm_sub_smul_lower_bound_infDist hD hz) hR₁
  have hadj : ‖adjoint B‖ = ‖B‖ := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint B
  have hc1 : ‖(adjoint B) ∘L (R ∘L B)‖ ≤ ‖adjoint B‖ * ‖R ∘L B‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hc2 : ‖R ∘L B‖ ≤ ‖R‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
  rw [hadj] at hc1
  have h3 : ‖B‖ * ((1 / delta) * ‖B‖) = ‖B‖ ^ 2 / delta := by field_simp
  nlinarith [norm_nonneg B, norm_nonneg R, norm_nonneg (R ∘L B)]

open ContinuousLinearMap in
/-- **Core spectral enclosure.** If `A - z` is bounded below by `cA`, the Feshbach correction has
norm at most `K < cA`, and `R` inverts `D - z`, then `z` is not in the spectrum of the block
operator `M = [[A, B*], [B, D]]`. -/
theorem spectral_enclosure_of_lower_bound {cA K : ℝ} (hR₁ : (D - z • 1) ∘L R = 1)
    (hR₂ : R ∘L (D - z • 1) = 1) (hAlow : ∀ a : U, cA * ‖a‖ ≤ ‖(A - z • 1) a‖)
    (hcorrOp : ‖(adjoint B) ∘L (R ∘L B)‖ ≤ K) (hlt : K < cA) :
    z ∉ spectrum 𝕜 (blockOp A (adjoint B) B D) := by
  have hcorr : ∀ a : U, ‖(adjoint B) (R (B a))‖ ≤ K * ‖a‖ := by
    intro a
    have h1 : ‖((adjoint B) ∘L (R ∘L B)) a‖ ≤ ‖(adjoint B) ∘L (R ∘L B)‖ * ‖a‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖(adjoint B) ∘L (R ∘L B)‖ * ‖a‖ ≤ K * ‖a‖ := by gcongr
    exact le_trans h1 h3
  have hFlow : ∀ a : U, (cA - K) * ‖a‖ ≤ ‖feshbachOp A (adjoint B) B z R a‖ := by
    intro a
    have h0 : feshbachOp A (adjoint B) B z R a = (A - z • 1) a - (adjoint B) (R (B a)) := rfl
    rw [h0]
    have h1 : ‖(A - z • 1) a‖ - ‖(adjoint B) (R (B a))‖
        ≤ ‖(A - z • 1) a - (adjoint B) (R (B a))‖ := norm_sub_norm_le _ _
    have h2 := hAlow a
    have h3 := hcorr a
    nlinarith
  have hzero : ∀ a : U, feshbachOp A (adjoint B) B z R a = 0 → a = 0 := by
    intro a ha
    have h1 := hFlow a
    rw [ha, norm_zero] at h1
    have h2 : ‖a‖ ≤ 0 := by nlinarith [norm_nonneg a]
    exact norm_eq_zero.mp (le_antisymm h2 (norm_nonneg a))
  have hker : ∀ x : WithLp 2 (U × W),
      x ∈ LinearMap.ker ((blockOp A (adjoint B) B D - z • 1 :
        WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) :
        WithLp 2 (U × W) →ₗ[𝕜] WithLp 2 (U × W)) → x = 0 := by
    intro x hx
    obtain ⟨hx2, hF⟩ := (mem_ker_blockOp_iff_feshbach hR₁ hR₂ x).mp hx
    have h1 : (WithLp.ofLp x).1 = 0 := hzero _ hF
    have h2 : (WithLp.ofLp x).2 = 0 := by rw [hx2, h1]; simp
    exact WithLp.ofLp_injective 2 (Prod.ext h1 h2)
  have hinj : Function.Injective
      (blockOp A (adjoint B) B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) := by
    intro x y hxy
    have h0 : (blockOp A (adjoint B) B D - z • 1 :
        WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) (LinearMap.mem_ker.mpr h0))
  have hu : IsUnit (blockOp A (adjoint B) B D - z • 1) := isUnit_of_injective hinj
  intro hmem
  rw [spectrum.mem_iff] at hmem
  refine hmem ?_
  have hneg : algebraMap 𝕜 (WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) z
      - blockOp A (adjoint B) B D = -(blockOp A (adjoint B) B D - z • 1) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [hneg]
  exact hu.neg

open ContinuousLinearMap in
/-- **Part B.5 — spectral enclosure.** If `z` is at distance at least `delta > 0` from the
spectrum of `D` and at distance strictly larger than `‖B‖ ^ 2 / delta` from the spectrum of `A`,
then `z` is not in the spectrum of the block operator `M = [[A, B*], [B, D]]`. -/
theorem feshbach_schur_spectral_enclosure {delta : ℝ} (hA : IsSelfAdjoint A)
    (hD : IsSelfAdjoint D) (hdelta : 0 < delta)
    (hzD : delta ≤ Metric.infDist z (spectrum 𝕜 D))
    (hzA : ‖B‖ ^ 2 / delta < Metric.infDist z (spectrum 𝕜 A)) :
    z ∉ spectrum 𝕜 (blockOp A (adjoint B) B D) := by
  obtain ⟨V, hV⟩ := isUnit_sub_smul_of_infDist hD hdelta hzD
  set S : W →L[𝕜] W := ↑V⁻¹ with hSdef
  have hR₁ : (D - z • 1) ∘L S = 1 := by rw [← hV]; exact V.mul_inv
  have hR₂ : S ∘L (D - z • 1) = 1 := by rw [← hV]; exact V.inv_mul
  exact spectral_enclosure_of_lower_bound hR₁ hR₂
    (norm_sub_smul_lower_bound_infDist hA le_rfl)
    (feshbach_schur_enclosure (B := B) hD hdelta hzD hR₁) hzA

open ContinuousLinearMap in
/-- The spectral enclosure in set form: the spectrum of `M = [[A, B*], [B, D]]` is contained in
the `delta`-neighbourhood of the spectrum of `D` together with the `‖B‖ ^ 2 / delta`-neighbourhood
of the spectrum of `A`. -/
theorem spectrum_blockOp_subset (hA : IsSelfAdjoint A) (hD : IsSelfAdjoint D) {delta : ℝ}
    (hdelta : 0 < delta) :
    spectrum 𝕜 (blockOp A (adjoint B) B D) ⊆
      {w : 𝕜 | Metric.infDist w (spectrum 𝕜 D) < delta} ∪
        {w : 𝕜 | Metric.infDist w (spectrum 𝕜 A) ≤ ‖B‖ ^ 2 / delta} := by
  intro w hw
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le] at hcon
  exact feshbach_schur_spectral_enclosure hA hD hdelta hcon.1 hcon.2 hw

end Enclosure

section CleanFibre

variable [CompleteSpace U] [CompleteSpace W]

/-- The fibre resolvent: on a clean blow-up the fibre block is the identity, `D = 1`, so for
`z ≠ 1` the resolvent `(D - z)⁻¹` is the scalar operator `(1 - z)⁻¹`. -/
noncomputable def fibreResolvent (W : Type*) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (z : 𝕜) : W →L[𝕜] W := (1 - z)⁻¹ • 1

omit [CompleteSpace W] in
theorem fibreResolvent_right (hz : z ≠ 1) :
    ((1 : W →L[𝕜] W) - z • 1) ∘L fibreResolvent W z = 1 := by
  have h : (1 : 𝕜) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  ext w
  simp only [fibreResolvent, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_smul]
  have hs : ((1 : 𝕜) - z)⁻¹ - z * (1 - z)⁻¹ = 1 := by field_simp
  rw [← sub_smul, hs, one_smul]

omit [CompleteSpace W] in
theorem fibreResolvent_left (hz : z ≠ 1) :
    fibreResolvent W z ∘L ((1 : W →L[𝕜] W) - z • 1) = 1 := by
  have h : (1 : 𝕜) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  ext w
  simp only [fibreResolvent, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_sub, smul_smul]
  have hs : ((1 : 𝕜) - z)⁻¹ • w - ((1 - z)⁻¹ * z) • w = w := by
    rw [← sub_smul]
    have : ((1 : 𝕜) - z)⁻¹ - (1 - z)⁻¹ * z = 1 := by field_simp
    rw [this, one_smul]
  exact hs

/-- **Part B.6 — the effective base operator** of a clean blow-up: eliminating the fibre
directions (on which the normalized Laplacian acts as the identity) replaces the base block `A`
by `A - (1 - z)⁻¹ B* B`. -/
noncomputable def effectiveBaseOp (A : U →L[𝕜] U) (B : U →L[𝕜] W) (z : 𝕜) : U →L[𝕜] U :=
  A - (1 - z)⁻¹ • ((ContinuousLinearMap.adjoint B) ∘L B)

open ContinuousLinearMap in
/-- The Feshbach map of a clean blow-up is `effectiveBaseOp A B z - z`. -/
theorem feshbachOp_fibre (A : U →L[𝕜] U) (B : U →L[𝕜] W) (z : 𝕜) :
    feshbachOp A (adjoint B) B z (fibreResolvent W z) = effectiveBaseOp A B z - z • 1 := by
  ext a
  simp [feshbachOp, effectiveBaseOp, fibreResolvent]
  abel

open ContinuousLinearMap in
theorem ker_feshbachOp_fibre (A : U →L[𝕜] U) (B : U →L[𝕜] W) (z : 𝕜) :
    LinearMap.ker ((feshbachOp A (adjoint B) B z (fibreResolvent W z) : U →L[𝕜] U) :
        U →ₗ[𝕜] U)
      = LinearMap.ker ((effectiveBaseOp A B z - z • 1 : U →L[𝕜] U) : U →ₗ[𝕜] U) := by
  rw [feshbachOp_fibre]

open ContinuousLinearMap in
/-- **Part B.6 — kernel reduction for a clean blow-up.** Away from `z = 1`, the kernel of
`M - z` is linearly isomorphic to the kernel of `effectiveBaseOp A B z - z`. -/
noncomputable def cleanFibre_kernel_equiv (A : U →L[𝕜] U) (B : U →L[𝕜] W) (hz : z ≠ 1) :
    LinearMap.ker ((blockOp A (adjoint B) B 1 - z • 1 :
        WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) :
        WithLp 2 (U × W) →ₗ[𝕜] WithLp 2 (U × W)) ≃ₗ[𝕜]
      LinearMap.ker ((effectiveBaseOp A B z - z • 1 : U →L[𝕜] U) : U →ₗ[𝕜] U) :=
  (feshbach_schur_kernel_equiv (A := A) (C := adjoint B) (B := B) (D := 1)
      (fibreResolvent_right hz) (fibreResolvent_left hz)).trans
    (LinearEquiv.ofEq _ _ (ker_feshbachOp_fibre A B z))

omit [CompleteSpace W] in
theorem norm_fibreResolvent_le (hz : z ≠ 1) : ‖fibreResolvent W z‖ ≤ 1 / ‖z - 1‖ := by
  have h : (1 : 𝕜) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h1 : ‖fibreResolvent W z‖ ≤ ‖((1 : 𝕜) - z)⁻¹‖ * ‖(1 : W →L[𝕜] W)‖ := by
    rw [fibreResolvent, norm_smul]
  have h2 : ‖(1 : W →L[𝕜] W)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h3 : ‖((1 : 𝕜) - z)⁻¹‖ = 1 / ‖z - 1‖ := by
    rw [norm_inv, ← norm_neg, neg_sub, one_div]
  nlinarith [norm_nonneg (((1 : 𝕜) - z)⁻¹), norm_nonneg (1 : W →L[𝕜] W),
    norm_nonneg (fibreResolvent W z)]

open ContinuousLinearMap in
/-- **Part B.6 — explicit enclosure away from `z = 1`.** The Feshbach correction of a clean
blow-up is bounded by `‖B‖ ^ 2 / ‖z - 1‖`. -/
theorem cleanFibre_enclosure (B : U →L[𝕜] W) (hz : z ≠ 1) :
    ‖(adjoint B) ∘L (fibreResolvent W z ∘L B)‖ ≤ ‖B‖ ^ 2 / ‖z - 1‖ := by
  have hne : ‖z - 1‖ ≠ 0 := by
    simpa [sub_eq_zero] using hz
  have hpos : 0 < ‖z - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hadj : ‖adjoint B‖ = ‖B‖ := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint B
  have hc1 : ‖(adjoint B) ∘L (fibreResolvent W z ∘L B)‖
      ≤ ‖adjoint B‖ * ‖fibreResolvent W z ∘L B‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have hc2 : ‖fibreResolvent W z ∘L B‖ ≤ ‖fibreResolvent W z‖ * ‖B‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hR := norm_fibreResolvent_le (W := W) hz
  rw [hadj] at hc1
  have h3 : ‖B‖ * ((1 / ‖z - 1‖) * ‖B‖) = ‖B‖ ^ 2 / ‖z - 1‖ := by field_simp
  nlinarith [norm_nonneg B, norm_nonneg (fibreResolvent W z),
    norm_nonneg (fibreResolvent W z ∘L B)]

open ContinuousLinearMap in
/-- **Part B.6 — spectral enclosure for a clean blow-up.** Away from `z = 1`, if `z` is farther
from the spectrum of the base block `A` than `‖B‖ ^ 2 / ‖z - 1‖`, then `z` is not in the spectrum
of the full operator. -/
theorem cleanFibre_spectral_enclosure [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 W]
    {A : U →L[𝕜] U} {B : U →L[𝕜] W} (hA : IsSelfAdjoint A) (hz : z ≠ 1)
    (hzA : ‖B‖ ^ 2 / ‖z - 1‖ < Metric.infDist z (spectrum 𝕜 A)) :
    z ∉ spectrum 𝕜 (blockOp A (adjoint B) B 1) :=
  spectral_enclosure_of_lower_bound (fibreResolvent_right hz) (fibreResolvent_left hz)
    (norm_sub_smul_lower_bound_infDist hA le_rfl) (cleanFibre_enclosure B hz) hzA

end CleanFibre

end PartB

end Brockian.ArithmeticFiber

