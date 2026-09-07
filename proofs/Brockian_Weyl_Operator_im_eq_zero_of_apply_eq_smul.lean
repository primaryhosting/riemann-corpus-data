/-
  Brockian/WeylOperator.lean — the abstract symmetric-operator / (essential)
  self-adjointness scaffolding underneath the **Weyl criterion**, built over
  Mathlib's partially-defined linear maps `H →ₗ.[ℂ] H` (`LinearPMap`).

  ## Setting

  `H` is a complex inner product space (physics convention: `⟪·,·⟫` is
  conjugate-linear in the FIRST argument). An unbounded operator is a
  densely-defined `T : H →ₗ.[ℂ] H`. Mathlib v4.32.0 supplies `LinearPMap.adjoint`
  and `LinearPMap.IsFormalAdjoint`, but *no* `LinearPMap.IsSymmetric`, no
  deficiency indices, and no essential-self-adjointness predicate. This file
  builds that missing layer and proves the genuinely-load-bearing lemmas.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `IsSymmetric T`                 — `T` is symmetric iff it is its own formal
                                        adjoint (`T.IsFormalAdjoint T`), i.e.
                                        `⟪T x, y⟫ = ⟪x, T y⟫` on the domain.
    * `IsSymmetric.inner_apply`       — that defining bilinear identity, unpacked.
    * `IsSymmetric.inner_self_im`     — **the quadratic form is real**:
                                        `(⟪T v, v⟫).im = 0`. (Real-spectrum core.)
    * `IsSymmetric.im_eq_zero_of_apply_eq_smul`
                                      — **eigenvalues of a symmetric operator are
                                        real**: `T v = μ • v`, `v ≠ 0 ⇒ μ.im = 0`.
    * `IsSymmetric.norm_sub_smul_ge`  — **the basic symmetric-operator
                                        inequality** `‖T v − z·v‖ ≥ |Im z|·‖v‖`
                                        for every `z : ℂ`. This is THE key
                                        genuinely-provable analytic fact: it is
                                        the identity `‖(T−z)v‖² = ‖(T−Re z)v‖² +
                                        (Im z)²‖v‖²` in disguise.
    * `IsSymmetric.eq_zero_of_apply_eq_smul`
                                      — consequence: for `Im z ≠ 0`, `T − z` is
                                        **injective on the domain**
                                        (`T v = z • v ⇒ v = 0`). This is why the
                                        nonreal spectral parameter never meets the
                                        point spectrum of a symmetric operator.
    * `deficiencySpace T z`           — the **deficiency space** `ker(T* − z)`,
                                        defined honestly as the kernel of the
                                        linear map `f ↦ T* f − z·f` on `dom(T*)`.
    * `mem_deficiencySpace_iff`       — its defining characterization
                                        `g ∈ 𝒟_z ↔ T* g = z • g` (eigenvectors of
                                        the adjoint). The space is not `{0}` by
                                        fiat — it is a genuine kernel.
    * `EssentiallySelfAdjoint T`      — the **Weyl-criterion predicate**: both
                                        deficiency spaces `ker(T* ∓ i)` are
                                        trivial. The real definition, not `True`.
    * `smulPMap c` / `smulPMap_isSymmetric` / `smulPMap_apply`
                                      — **Gate-0 witness**: the everywhere-defined
                                        real-scalar operator `x ↦ c·x` (`c : ℝ`)
                                        is symmetric, instantiating the whole
                                        framework non-vacuously (`c = 1` is the
                                        identity). Its inequality and injectivity
                                        corollaries then hold by the theorems
                                        above.

  ## What is NOT proved, and why (honest scope statement)

  The Weyl criterion *itself* — "symmetric `T` is essentially self-adjoint iff
  both deficiency spaces vanish" — is **not** proved. It requires von Neumann's
  extension theory (the closure `T̄ = T**`, the Cayley transform, the
  identification of self-adjoint extensions with partial isometries between the
  deficiency spaces), none of which exists in Mathlib v4.32.0. Likewise we do
  not prove the bounded witness `smulPMap c` *is* essentially self-adjoint:
  that needs the adjoint of a `LinearMap.toPMap` computed explicitly (that
  `(smulPMap c)* = smulPMap c`), a `LinearPMap.adjoint` identity Mathlib does not
  provide. The predicate `EssentiallySelfAdjoint` is nonetheless the genuine
  mathematical one; this file ships the verified inequality/real-spectrum rung on
  which the criterion is built, and names nothing it does not prove.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Brockian.Weyl.Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Symmetric densely-defined operators -/

/-- **Symmetric operator.** A partially-defined operator `T : H →ₗ.[ℂ] H` is
*symmetric* when it is its own formal adjoint: `⟪T x, y⟫ = ⟪x, T y⟫` for all
`x, y` in the domain. This is the honest `LinearPMap` formulation (Mathlib has
`IsFormalAdjoint` but no `IsSymmetric`). -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

/-- The defining identity of a symmetric operator, unpacked. -/
theorem IsSymmetric.inner_apply {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (x y : T.domain) : ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ := hT x y

/-- **The quadratic form of a symmetric operator is real.** For any `v` in the
domain, `⟪T v, v⟫` has zero imaginary part. This is the seed of the "spectrum is
real" phenomenon: from it both real eigenvalues and the basic inequality below
follow. -/
theorem IsSymmetric.inner_self_im {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) : (⟪T v, (v : H)⟫_ℂ).im = 0 := by
  have h1 : ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ := hT v v
  have h2 : (starRingEnd ℂ) ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ :=
    inner_conj_symm (v : H) (T v)
  rw [← h1] at h2
  rwa [Complex.conj_eq_iff_im] at h2

/-- **Eigenvalues of a symmetric operator are real.** If `T v = μ • v` for a
nonzero `v` in the domain, then `μ` is real (`μ.im = 0`). -/
theorem IsSymmetric.im_eq_zero_of_apply_eq_smul {T : H →ₗ.[ℂ] H}
    (hT : IsSymmetric T) {v : T.domain} {μ : ℂ} (hv : (v : H) ≠ 0)
    (heig : T v = μ • (v : H)) : μ.im = 0 := by
  have hb := hT.inner_self_im v
  rw [heig, inner_smul_left] at hb
  set s : ℂ := ⟪(v : H), (v : H)⟫_ℂ with hs
  have hsim : s.im = 0 := by
    have hc : (starRingEnd ℂ) s = s := inner_conj_symm (v : H) (v : H)
    rwa [Complex.conj_eq_iff_im] at hc
  have hsre : s.re = ‖(v : H)‖ ^ 2 := by rw [hs]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (v : H)
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hsim] at hb
  have hsrepos : (0 : ℝ) < s.re := by rw [hsre]; positivity
  have hz : μ.im * s.re = 0 := by linear_combination -hb
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hsrepos)

/-! ### The basic symmetric-operator inequality -/

/-- **The basic symmetric-operator inequality** `‖T v − z·v‖ ≥ |Im z|·‖v‖`.

For a symmetric `T`, every `z : ℂ`, and every `v` in the domain. This is the
analytic heart of the whole self-adjointness story: it is the Pythagorean
identity
    `‖(T − z)v‖² = ‖(T − Re z)v‖² + (Im z)²‖v‖²`
(valid because `⟪T v, v⟫` is real), from which we read off `≥ (Im z)²‖v‖²` and
take square roots. When `Im z ≠ 0` it forces `T − z` injective (below) and, in
the closed case, boundedly-invertible onto its range. -/
theorem IsSymmetric.norm_sub_smul_ge {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) (z : ℂ) : |z.im| * ‖(v : H)‖ ≤ ‖T v - z • (v : H)‖ := by
  set u : H := T v with hu
  set w : H := (v : H) with hw
  -- `⟪u, w⟫` is real (quadratic form of a symmetric operator)
  have hc : (⟪u, w⟫_ℂ).im = 0 := hT.inner_self_im v
  -- component identities for the complex scalar `z`
  have hnormz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  have hnormzr : ‖(z.re : ℂ)‖ = |z.re| := by simp
  -- expand both norms via the (RCLike) parallelogram/`norm_sub_sq` formula
  have e1 : ‖u - z • w‖ ^ 2 = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, z • w⟫_ℂ) + ‖z • w‖ ^ 2 :=
    norm_sub_sq u (z • w)
  have e2 : ‖u - (z.re : ℂ) • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, (z.re : ℂ) • w⟫_ℂ) + ‖(z.re : ℂ) • w‖ ^ 2 :=
    norm_sub_sq u _
  rw [inner_smul_right, norm_smul] at e1
  rw [inner_smul_right, norm_smul, hnormzr] at e2
  -- the real parts of the cross terms coincide (imaginary part of `⟪u,w⟫` drops out)
  have hr1 : RCLike.re (z * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show (z * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; ring
  have hr2 : RCLike.re ((z.re : ℂ) * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show ((z.re : ℂ) * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; simp
  rw [hr1] at e1; rw [hr2] at e2
  -- the Pythagorean split identity
  have key : ‖u - z • w‖ ^ 2 = ‖u - (z.re : ℂ) • w‖ ^ 2 + z.im ^ 2 * ‖w‖ ^ 2 := by
    rw [e1, e2]
    have ha : (‖z‖ * ‖w‖) ^ 2 = (z.re ^ 2 + z.im ^ 2) * ‖w‖ ^ 2 := by rw [mul_pow, hnormz]
    have hb : (|z.re| * ‖w‖) ^ 2 = z.re ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [ha, hb]; ring
  -- read off the squared inequality, then take square roots
  have hge : z.im ^ 2 * ‖w‖ ^ 2 ≤ ‖u - z • w‖ ^ 2 := by
    rw [key]; nlinarith [sq_nonneg ‖u - (z.re : ℂ) • w‖]
  have hA : (0 : ℝ) ≤ |z.im| * ‖w‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hsq : (|z.im| * ‖w‖) ^ 2 = z.im ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
  calc |z.im| * ‖w‖ = Real.sqrt ((|z.im| * ‖w‖) ^ 2) := (Real.sqrt_sq hA).symm
    _ = Real.sqrt (z.im ^ 2 * ‖w‖ ^ 2) := by rw [hsq]
    _ ≤ Real.sqrt (‖u - z • w‖ ^ 2) := Real.sqrt_le_sqrt hge
    _ = ‖u - z • w‖ := Real.sqrt_sq (norm_nonneg _)

/-- **`T − z` is injective on the domain for nonreal `z`.** If `T` is symmetric,
`Im z ≠ 0`, and `T v = z • v`, then `v = 0`. Immediate from the basic inequality
(a nonzero eigenvector at `z` would force `|Im z|·‖v‖ ≤ 0`). -/
theorem IsSymmetric.eq_zero_of_apply_eq_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {z : ℂ} (hz : z.im ≠ 0) {v : T.domain} (h : T v = z • (v : H)) :
    (v : H) = 0 := by
  have hineq := hT.norm_sub_smul_ge v z
  rw [h, sub_self, norm_zero] at hineq
  have h1 : |z.im| * ‖(v : H)‖ = 0 :=
    le_antisymm hineq (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (abs_eq_zero.mp h2) hz
  · exact norm_eq_zero.mp h2

/-! ### Deficiency spaces and essential self-adjointness -/

section Adjoint

variable [CompleteSpace H]

/-- **The deficiency space `ker(T* − z)`.** For a densely-defined `T`, the
adjoint `T* = T.adjoint` is a `LinearPMap`; the deficiency space at `z` is the
kernel of the honest linear map `f ↦ T* f − z·f` on `dom(T*)`. It is *not*
`{0}` by fiat — it is a genuine kernel, and it measures the failure of essential
self-adjointness (Weyl / von Neumann). -/
noncomputable def deficiencySpace (T : H →ₗ.[ℂ] H) (z : ℂ) :
    Submodule ℂ T.adjoint.domain :=
  LinearMap.ker (T.adjoint.toFun - z • T.adjoint.domain.subtype)

/-- **Deficiency-space membership = eigenvector of the adjoint.**
`g ∈ ker(T* − z) ↔ T* g = z • g`. Confirms the definition is the real one. -/
theorem mem_deficiencySpace_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (g : T.adjoint.domain) :
    g ∈ deficiencySpace T z ↔ T.adjoint g = z • (g : H) := by
  rw [deficiencySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, sub_eq_zero]
  rfl

/-- **Essential self-adjointness (the Weyl-criterion predicate).** A symmetric
operator is essentially self-adjoint exactly when both deficiency spaces
`ker(T* ∓ i)` are trivial. This is the genuine predicate the Weyl limit-point
criterion certifies — not a placeholder. -/
def EssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop :=
  deficiencySpace T Complex.I = ⊥ ∧ deficiencySpace T (-Complex.I) = ⊥

end Adjoint

/-! ### Gate-0 witness: a concrete symmetric operator -/

/-- **The everywhere-defined real-scalar operator** `x ↦ (c : ℝ) • x`, packaged
as a `LinearPMap` with full domain `⊤`. For `c = 1` this is the identity. -/
noncomputable def smulPMap (c : ℝ) : H →ₗ.[ℂ] H := ((c : ℂ) • LinearMap.id).toPMap ⊤

/-- The witness acts as multiplication by the real scalar `c`. -/
@[simp] theorem smulPMap_apply (c : ℝ) (x : (smulPMap (H := H) c).domain) :
    (smulPMap c) x = (c : ℂ) • (x : H) := by
  simp [smulPMap, LinearMap.toPMap_apply]

/-- The witness is everywhere defined (domain `= ⊤`), hence densely defined. -/
theorem smulPMap_domain (c : ℝ) : (smulPMap (H := H) c).domain = ⊤ := by
  simp [smulPMap, LinearMap.toPMap]

/-- **Gate-0 (non-vacuity).** The real-scalar operator `smulPMap c` is symmetric,
instantiating `IsSymmetric` — and hence the inequality `norm_sub_smul_ge`, the
real-spectrum lemmas, and the injectivity corollary — on a genuine, nonzero
operator. So none of the framework is vacuous. -/
theorem smulPMap_isSymmetric (c : ℝ) : IsSymmetric (smulPMap (H := H) c) := by
  intro x y
  rw [smulPMap_apply, smulPMap_apply, inner_smul_left, inner_smul_right]
  simp

end Brockian.Weyl.Operator
