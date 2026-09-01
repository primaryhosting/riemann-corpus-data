/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/
theorem isCompactOperator_of_approx {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : H →L[ℂ] H)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧
      ∀ y : H, ‖y‖ ≤ 1 → ∃ v ∈ V, ‖R y - v‖ ≤ ε) :
    IsCompactOperator R := by
  set S : Set H := (R : H → H) '' Metric.closedBall 0 1 with hS
  have htb : TotallyBounded S := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨V, hVfin, hV⟩ := happrox (ε / 3) (by linarith)
    have hWcompact : IsCompact ((V.subtype) '' (Metric.closedBall (0 : V) (‖R‖ + ε))) :=
      (isCompact_closedBall _ _).image continuous_subtype_val
    obtain ⟨t, htfin, htcover⟩ :=
      Metric.totallyBounded_iff.mp hWcompact.totallyBounded (ε / 3) (by linarith)
    refine ⟨t, htfin, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    obtain ⟨v, hvV, hv⟩ := hV y hy1
    have hRy : ‖R y‖ ≤ ‖R‖ := by
      have h := R.le_opNorm y
      have h2 := R.opNorm_nonneg
      nlinarith
    have hvnorm : ‖v‖ ≤ ‖R‖ + ε := by
      have h3 : ‖v‖ ≤ ‖R y‖ + ‖R y - v‖ := by
        calc ‖v‖ = ‖R y - (R y - v)‖ := by congr 1; abel
          _ ≤ ‖R y‖ + ‖R y - v‖ := norm_sub_le _ _
      linarith
    have hvW : v ∈ (V.subtype) '' (Metric.closedBall (0 : V) (‖R‖ + ε)) := by
      refine ⟨⟨v, hvV⟩, ?_, rfl⟩
      simpa using hvnorm
    obtain ⟨w, hwt, hw⟩ := Set.mem_iUnion₂.mp (htcover hvW)
    refine Set.mem_iUnion₂.mpr ⟨w, hwt, ?_⟩
    have hd1 : dist (R y) v ≤ ε / 3 := by rw [dist_eq_norm]; exact hv
    have hd2 : dist v w < ε / 3 := by simpa [Metric.mem_ball] using hw
    have h4 : dist (R y) w ≤ dist (R y) v + dist v w := dist_triangle _ _ _
    simp only [Metric.mem_ball]
    linarith
  have hcpt : IsCompact (closure S) := htb.closure.isCompact_of_isClosed isClosed_closure
  exact (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image (R : H → H)).mpr
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos, hcpt⟩

end Brockian.Weyl.OscillatorCompact

/-
  Base.lean — reconstruction of the corpus modules that the target theorem
  depends on:

  * `Brockian/WeylOperator.lean`            (verbatim)
  * `Brockian/WeylSchrodingerMinimal.lean`  (the L² / Schwartz-core scaffolding
                                             used by the harmonic oscillator)
  * `Brockian/WeylHarmonicOscillator.lean`  (verbatim, minus the
                                             `CompactResolventShape` statements,
                                             which the target does not use)
-/
import Mathlib

/-! ## Brockian/WeylOperator.lean -/

namespace Brockian.Weyl.Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Symmetric operator.** A partially-defined operator `T : H →ₗ.[ℂ] H` is
*symmetric* when it is its own formal adjoint: `⟪T x, y⟫ = ⟪x, T y⟫` for all
`x, y` in the domain. -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

/-- The defining identity of a symmetric operator, unpacked. -/
theorem IsSymmetric.inner_apply {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (x y : T.domain) : ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ := hT x y

/-- **The quadratic form of a symmetric operator is real.** -/
theorem IsSymmetric.inner_self_im {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) : (⟪T v, (v : H)⟫_ℂ).im = 0 := by
  have h1 : ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ := hT v v
  have h2 : (starRingEnd ℂ) ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ :=
    inner_conj_symm (v : H) (T v)
  rw [← h1] at h2
  rwa [Complex.conj_eq_iff_im] at h2

/-- **Eigenvalues of a symmetric operator are real.** -/
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

/-- **The basic symmetric-operator inequality** `‖T v − z·v‖ ≥ |Im z|·‖v‖`. -/
theorem IsSymmetric.norm_sub_smul_ge {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) (z : ℂ) : |z.im| * ‖(v : H)‖ ≤ ‖T v - z • (v : H)‖ := by
  set u : H := T v with hu
  set w : H := (v : H) with hw
  have hc : (⟪u, w⟫_ℂ).im = 0 := hT.inner_self_im v
  have hnormz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  have hnormzr : ‖(z.re : ℂ)‖ = |z.re| := by simp
  have e1 : ‖u - z • w‖ ^ 2 = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, z • w⟫_ℂ) + ‖z • w‖ ^ 2 :=
    norm_sub_sq u (z • w)
  have e2 : ‖u - (z.re : ℂ) • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, (z.re : ℂ) • w⟫_ℂ) + ‖(z.re : ℂ) • w‖ ^ 2 :=
    norm_sub_sq u _
  rw [inner_smul_right, norm_smul] at e1
  rw [inner_smul_right, norm_smul, hnormzr] at e2
  have hr1 : RCLike.re (z * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show (z * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; ring
  have hr2 : RCLike.re ((z.re : ℂ) * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show ((z.re : ℂ) * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; simp
  rw [hr1] at e1; rw [hr2] at e2
  have key : ‖u - z • w‖ ^ 2 = ‖u - (z.re : ℂ) • w‖ ^ 2 + z.im ^ 2 * ‖w‖ ^ 2 := by
    rw [e1, e2]
    have ha : (‖z‖ * ‖w‖) ^ 2 = (z.re ^ 2 + z.im ^ 2) * ‖w‖ ^ 2 := by rw [mul_pow, hnormz]
    have hb : (|z.re| * ‖w‖) ^ 2 = z.re ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [ha, hb]; ring
  have hge : z.im ^ 2 * ‖w‖ ^ 2 ≤ ‖u - z • w‖ ^ 2 := by
    rw [key]; nlinarith [sq_nonneg ‖u - (z.re : ℂ) • w‖]
  have hA : (0 : ℝ) ≤ |z.im| * ‖w‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hsq : (|z.im| * ‖w‖) ^ 2 = z.im ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
  calc |z.im| * ‖w‖ = Real.sqrt ((|z.im| * ‖w‖) ^ 2) := (Real.sqrt_sq hA).symm
    _ = Real.sqrt (z.im ^ 2 * ‖w‖ ^ 2) := by rw [hsq]
    _ ≤ Real.sqrt (‖u - z • w‖ ^ 2) := Real.sqrt_le_sqrt hge
    _ = ‖u - z • w‖ := Real.sqrt_sq (norm_nonneg _)

/-- **`T − z` is injective on the domain for nonreal `z`.** -/
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

section Adjoint

variable [CompleteSpace H]

/-- **The deficiency space `ker(T* − z)`.** -/
noncomputable def deficiencySpace (T : H →ₗ.[ℂ] H) (z : ℂ) :
    Submodule ℂ T.adjoint.domain :=
  LinearMap.ker (T.adjoint.toFun - z • T.adjoint.domain.subtype)

/-- **Deficiency-space membership = eigenvector of the adjoint.** -/
theorem mem_deficiencySpace_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (g : T.adjoint.domain) :
    g ∈ deficiencySpace T z ↔ T.adjoint g = z • (g : H) := by
  rw [deficiencySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, sub_eq_zero]
  rfl

/-- **Essential self-adjointness (the Weyl-criterion predicate).** -/
def EssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop :=
  deficiencySpace T Complex.I = ⊥ ∧ deficiencySpace T (-Complex.I) = ⊥

end Adjoint

/-- **The everywhere-defined real-scalar operator** `x ↦ (c : ℝ) • x`. -/
noncomputable def smulPMap (c : ℝ) : H →ₗ.[ℂ] H := ((c : ℂ) • LinearMap.id).toPMap ⊤

/-- The witness acts as multiplication by the real scalar `c`. -/
@[simp] theorem smulPMap_apply (c : ℝ) (x : (smulPMap (H := H) c).domain) :
    (smulPMap c) x = (c : ℂ) • (x : H) := by
  simp [smulPMap, LinearMap.toPMap_apply]

/-- The witness is everywhere defined (domain `= ⊤`), hence densely defined. -/
theorem smulPMap_domain (c : ℝ) : (smulPMap (H := H) c).domain = ⊤ := by
  simp [smulPMap, LinearMap.toPMap]

/-- **Gate-0 (non-vacuity).** -/
theorem smulPMap_isSymmetric (c : ℝ) : IsSymmetric (smulPMap (H := H) c) := by
  intro x y
  rw [smulPMap_apply, smulPMap_apply, inner_smul_left, inner_smul_right]
  simp

end Brockian.Weyl.Operator

/-! ## Brockian/WeylSchrodingerMinimal.lean (reconstruction)

The minimal `L²(ℝ)` scaffolding: the Hilbert space, the Schwartz core embedding,
the second-derivative operator on the Schwartz space and the symmetry of the
kinetic term (integration by parts). -/

namespace Brockian.Weyl.SchrodingerMinimal

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

/-- The Hilbert space `L²(ℝ, ℂ)`. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The Schwartz core of `L²(ℝ)`. -/
noncomputable def schwartzToL2 : SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

@[simp] theorem schwartzToL2_apply (f : SchwartzMap ℝ ℂ) :
    schwartzToL2 f = f.toLp 2 (volume : Measure ℝ) := rfl

theorem schwartzToL2_injective : Function.Injective schwartzToL2 :=
  SchwartzMap.injective_toLp 2 (volume : Measure ℝ)

theorem inner_toLp (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 f) (schwartzToL2 g) = ∫ x : ℝ, conj (f x) * g x := by
  have h := SchwartzMap.inner_toL2_toL2_eq f g (volume : Measure ℝ)
  rw [schwartzToL2_apply, schwartzToL2_apply, h]
  simp [RCLike.inner_apply, mul_comm]

/-- Products of Schwartz functions are integrable. -/
theorem integrable_conj_mul (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => conj (f x) * g x) volume := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  have hmeas : AEStronglyMeasurable (fun x : ℝ => conj (f x)) volume :=
    (Complex.continuous_conj.comp f.continuous).aestronglyMeasurable
  refine Integrable.bdd_mul (c := C) g.integrable hmeas
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using hC x

theorem integrable_mul (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => f x * g x) volume := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  refine Integrable.bdd_mul (c := C) g.integrable f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using hC x

/-- **Integration by parts on the Schwartz space.** -/
theorem integral_conj_mul_deriv (u v : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, conj (u x) * deriv (v : ℝ → ℂ) x
      = -∫ x : ℝ, conj (deriv (u : ℝ → ℂ) x) * v x := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y => conj (u y)) (conj (deriv (u : ℝ → ℂ) x)) x := by
    intro x
    have h := (u.differentiable.differentiableAt (x := x)).hasDerivAt
    simpa using h.star
  have hv : ∀ x : ℝ, HasDerivAt (v : ℝ → ℂ) (deriv (v : ℝ → ℂ) x) x :=
    fun x => (v.differentiable.differentiableAt (x := x)).hasDerivAt
  have hdv : (deriv (v : ℝ → ℂ)) = ((SchwartzMap.derivCLM ℂ ℂ v : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext x; rw [SchwartzMap.derivCLM_apply]
  have hdu : (deriv (u : ℝ → ℂ)) = ((SchwartzMap.derivCLM ℂ ℂ u : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext x; rw [SchwartzMap.derivCLM_apply]
  have h1 : Integrable ((fun x => conj (u x)) * deriv (v : ℝ → ℂ)) volume := by
    rw [hdv]; exact integrable_conj_mul u (SchwartzMap.derivCLM ℂ ℂ v)
  have h2 : Integrable ((fun x => conj (deriv (u : ℝ → ℂ) x)) * (v : ℝ → ℂ)) volume := by
    rw [hdu]; exact integrable_conj_mul (SchwartzMap.derivCLM ℂ ℂ u) v
  have h3 : Integrable ((fun x => conj (u x)) * (v : ℝ → ℂ)) volume := integrable_conj_mul u v
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv h1 h2 h3

/-- The second derivative as a continuous linear map on the Schwartz space. -/
noncomputable def D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ)

@[simp] theorem D2_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    D2 f x = deriv (deriv (f : ℝ → ℂ)) x := by
  have hdf : ((SchwartzMap.derivCLM ℂ ℂ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (f : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  show (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) x = _
  rw [SchwartzMap.derivCLM_apply, hdf]

/-- The kinetic term is symmetric on the Schwartz core. -/
theorem kinetic_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 (D2 f)) (schwartzToL2 g)
      = inner ℂ (schwartzToL2 f) (schwartzToL2 (D2 g)) := by
  rw [inner_toLp, inner_toLp]
  simp only [D2_apply]
  have hdf : ((SchwartzMap.derivCLM ℂ ℂ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (f : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  have hdg : ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (g : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  have h1 := integral_conj_mul_deriv (SchwartzMap.derivCLM ℂ ℂ f) g
  rw [hdf] at h1
  have h2 := integral_conj_mul_deriv f (SchwartzMap.derivCLM ℂ ℂ g)
  rw [hdg] at h2
  linear_combination h1 - h2

end Brockian.Weyl.SchrodingerMinimal

/-! ## Brockian/WeylHarmonicOscillator.lean -/

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- Multiplication by `x^2` preserves Schwartz space. -/
noncomputable def quadraticMulSchwartz :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x ^ 2 : ℂ))

theorem quadratic_hasTemperateGrowth :
    (fun x : ℝ => (x ^ 2 : ℂ)).HasTemperateGrowth := by
  fun_prop

@[simp] theorem quadraticMulSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    quadraticMulSchwartz f x = (x ^ 2 : ℂ) * f x := by
  rw [quadraticMulSchwartz]
  simpa [smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply quadratic_hasTemperateGrowth f x

/-- The harmonic-oscillator action on Schwartz functions. -/
noncomputable def oscillatorSchwartz :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  -D2 + quadraticMulSchwartz

@[simp] theorem oscillatorSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    oscillatorSchwartz f x = -deriv (deriv f) x + (x ^ 2 : ℂ) * f x := by
  simp [oscillatorSchwartz, D2_apply]

/-- The harmonic-oscillator core action, valued in `L2(R)`. -/
noncomputable def oscillatorCoreMap : SchwartzMap ℝ ℂ →ₗ[ℂ] L2R :=
  schwartzToL2.comp oscillatorSchwartz.toLinearMap

@[simp] theorem oscillatorCoreMap_apply (f : SchwartzMap ℝ ℂ) :
    oscillatorCoreMap f = schwartzToL2 (oscillatorSchwartz f) := rfl

theorem oscillatorCoreMap_expanded (f : SchwartzMap ℝ ℂ) :
    oscillatorCoreMap f =
      -(schwartzToL2 (D2 f)) + schwartzToL2 (quadraticMulSchwartz f) := by
  show schwartzToL2 (oscillatorSchwartz f) = _
  rw [oscillatorSchwartz]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, map_add, map_neg]

/-- The minimal harmonic oscillator `-d^2/dx^2 + x^2` on the Schwartz core. -/
noncomputable def harmonicOscillatorPMap : L2R →ₗ.[ℂ] L2R where
  domain := LinearMap.range schwartzToL2
  toFun := oscillatorCoreMap.comp
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap

@[simp] theorem harmonicOscillatorPMap_domain :
    harmonicOscillatorPMap.domain = LinearMap.range schwartzToL2 := rfl

/-- Exact action on an embedded Schwartz function. -/
theorem harmonicOscillatorPMap_toFun_ofInjective (f : SchwartzMap ℝ ℂ) :
    harmonicOscillatorPMap
        (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = oscillatorCoreMap f := by
  show oscillatorCoreMap.comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = oscillatorCoreMap f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

/-- The harmonic oscillator has a dense Schwartz domain. -/
theorem harmonicOscillatorPMap_dense :
    Dense (harmonicOscillatorPMap.domain : Set L2R) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → L2R)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f
    rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [harmonicOscillatorPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

/-- Multiplication by the real function `x^2` is symmetric on the Schwartz core. -/
theorem quadraticMul_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 (quadraticMulSchwartz f)) (schwartzToL2 g) =
      inner ℂ (schwartzToL2 f) (schwartzToL2 (quadraticMulSchwartz g)) := by
  rw [inner_toLp, inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [quadraticMulSchwartz_apply, map_mul, map_pow, Complex.conj_ofReal]
  ring

/-- The full oscillator action is symmetric on Schwartz functions. -/
theorem oscillatorCoreMap_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (oscillatorCoreMap f) (schwartzToL2 g) =
      inner ℂ (schwartzToL2 f) (oscillatorCoreMap g) := by
  rw [oscillatorCoreMap_expanded, oscillatorCoreMap_expanded,
    inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    kinetic_symm f g, quadraticMul_symm f g]

/-- The concrete minimal harmonic oscillator is symmetric. -/
theorem harmonicOscillatorPMap_isSymmetric :
    IsSymmetric harmonicOscillatorPMap := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, harmonicOscillatorPMap_toFun_ofInjective,
    harmonicOscillatorPMap_toFun_ofInjective, LinearEquiv.ofInjective_apply,
    LinearEquiv.ofInjective_apply]
  exact oscillatorCoreMap_symm f g

end Brockian.Weyl.HarmonicOscillator

/-
  OscillatorDiscrete.lean — `Brockian/WeylOscillatorDiscrete.lean` together with
  the target theorem: the two canonical unit-shift resolvents of the harmonic
  oscillator closure are compact operators.
-/
import RequestProject.Compactness

namespace Brockian.Weyl.OscillatorDiscrete

open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.ClosedShiftedRanges
open Brockian.Weyl.WeightedRellich
open Brockian.Weyl.HarmonicOscillator
open Brockian.Weyl.OscillatorCompact

variable {H Eadd Esub : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Eadd] [NormedSpace ℂ Eadd]
  [NormedAddCommGroup Esub] [NormedSpace ℂ Esub]

/-- Both canonical unit-shift resolvents of an operator, together with proofs
that they are compact operators. -/
structure CompactResolventAtI (T : H →ₗ.[ℂ] H) where
  resolvent : ResolventAtI T
  compact_add : IsCompactOperator resolvent.Radd
  compact_sub : IsCompactOperator resolvent.Rsub

/-- Weighted-Rellich factorizations construct a compact-resolvent package. -/
def CompactResolventAtI.ofFactorizations {T : H →ₗ.[ℂ] H}
    (hres : ResolventAtI T)
    (Fadd : Factorization hres.Radd Eadd)
    (Fsub : Factorization hres.Rsub Esub) : CompactResolventAtI T where
  resolvent := hres
  compact_add := Fadd.isCompactOperator
  compact_sub := Fsub.isCompactOperator

/-- The canonical unit-shift resolvents on the self-adjoint closure of an
essentially self-adjoint harmonic-oscillator core. -/
noncomputable def harmonicOscillatorClosureResolventAtI
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap) :
    ResolventAtI harmonicOscillatorPMap.closure :=
  closureResolventAtIOfEssentiallySelfAdjoint
    harmonicOscillatorPMap_isSymmetric harmonicOscillatorPMap_dense hESA

/-- **The concrete weighted-Rellich endpoint.** Both canonical unit-shift
resolvents `(T̄ ± i)⁻¹` of the closure of the harmonic-oscillator core are
compact operators. -/
theorem harmonicOscillatorClosureResolvents_compact_target
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap) :
    IsCompactOperator (harmonicOscillatorClosureResolventAtI hESA).Radd ∧
      IsCompactOperator (harmonicOscillatorClosureResolventAtI hESA).Rsub := by
  have hsym : IsSymmetric harmonicOscillatorPMap.closure :=
    isSymmetric_closure harmonicOscillatorPMap_isSymmetric harmonicOscillatorPMap_dense
  constructor
  · refine isCompactOperator_of_rightResolvent (z := -Complex.I) (by simp) (by simp)
      ?_ hsym
    exact (harmonicOscillatorClosureResolventAtI hESA).right_add
  · refine isCompactOperator_of_rightResolvent (z := Complex.I) (by simp) (by simp)
      ?_ hsym
    exact (harmonicOscillatorClosureResolventAtI hESA).right_sub

end Brockian.Weyl.OscillatorDiscrete

/-
  Compactness.lean — the concrete weighted-Rellich estimate for the harmonic
  oscillator core, and the compactness of the two unit-shift resolvents of its
  closure.

  The mathematical content:

  * `energy g = ∫ ‖g'‖² + ∫ x²‖g‖²` is the quadratic form of the oscillator on
    the Schwartz core (`inner_oscillatorCoreMap_self`).
  * The image of the closed unit ball under a unit-shift resolvent of the
    closure consists of `L²`-limits of Schwartz functions of energy at most `2`
    (`resolvent_mem_closure_goodSet`).
  * A set of Schwartz functions of bounded energy is, in `L²`, uniformly close
    to a fixed finite-dimensional subspace of step functions: the confining
    weight `x²` controls the tail and the kinetic term controls the oscillation
    inside each cell (`exists_finiteDimensional_approx`).
  * An operator whose unit ball image is uniformly approximable by
    finite-dimensional subspaces is compact (`isCompactOperator_of_approx`).
-/
import RequestProject.ClosureResolvent
import RequestProject.CompactCriterion
import RequestProject.Rellich

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.OscillatorCompact

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.HarmonicOscillator
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.ClosedShiftedRanges
open Filter Topology

/-! ### The quadratic form of the oscillator -/

/-- The quadratic form of the harmonic oscillator on the Schwartz core is the
energy. -/
theorem inner_oscillatorCoreMap_self (g : SchwartzMap ℝ ℂ) :
    inner ℂ (oscillatorCoreMap g) (schwartzToL2 g) = (energy g : ℂ) := by
  rw [oscillatorCoreMap_expanded, inner_add_left, inner_neg_left, inner_toLp, inner_toLp]
  have hdg : ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (g : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  -- the kinetic term
  have hkin := integral_conj_mul_deriv (SchwartzMap.derivCLM ℂ ℂ g) g
  rw [hdg] at hkin
  have hkin2 : -∫ x : ℝ, conj (D2 g x) * g x
      = ((∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    have hD2 : ∫ x : ℝ, conj (D2 g x) * g x
        = ∫ x : ℝ, conj (deriv (deriv (g : ℝ → ℂ)) x) * g x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [D2_apply]
    rw [hD2, ← hkin, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact conj_mul_self _
  -- the potential term
  have hpot : ∫ x : ℝ, conj (quadraticMulSchwartz g x) * g x
      = ((∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [quadraticMulSchwartz_apply]
    rw [map_mul, map_pow, Complex.conj_ofReal, mul_assoc, conj_mul_self]
    push_cast
    ring
  rw [hpot, energy]
  push_cast
  rw [hkin2]

/-! ### The set of Schwartz states of bounded energy -/

/-- The approximation property passes to the closure. -/
theorem exists_approx_of_mem_closure {C ε : ℝ} (hε : 0 < ε)
    {V : Submodule ℂ L2R} (hV : ∀ u ∈ goodSet C, ∃ v ∈ V, ‖u - v‖ ≤ ε)
    {u : L2R} (hu : u ∈ closure (goodSet C)) : ∃ v ∈ V, ‖u - v‖ ≤ 2 * ε := by
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp hu ε hε
  obtain ⟨v, hvV, hv⟩ := hV w hw
  refine ⟨v, hvV, ?_⟩
  have h1 : ‖u - w‖ ≤ ε := by
    rw [← dist_eq_norm]; exact hdist.le
  calc ‖u - v‖ = ‖(u - w) + (w - v)‖ := by congr 1; abel
    _ ≤ ‖u - w‖ + ‖w - v‖ := norm_add_le _ _
    _ ≤ ε + ε := add_le_add h1 hv
    _ = 2 * ε := by ring

/-! ### The resolvent maps the unit ball into the good set -/

/-- Every element of the oscillator core domain comes from a Schwartz
function. -/
theorem exists_schwartz_of_mem_domain (v : harmonicOscillatorPMap.domain) :
    ∃ g : SchwartzMap ℝ ℂ, (v : L2R) = schwartzToL2 g ∧
      harmonicOscillatorPMap v = oscillatorCoreMap g := by
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp v.2
  refine ⟨g, hg.symm, ?_⟩
  have hve : v = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hve, harmonicOscillatorPMap_toFun_ofInjective]

/-- Elements of the domain of the closure are graph limits of Schwartz
functions. -/
theorem exists_seq_schwartz_tendsto
    (u : (harmonicOscillatorPMap.closure).domain) :
    ∃ g : ℕ → SchwartzMap ℝ ℂ,
      Tendsto (fun n => schwartzToL2 (g n)) atTop (𝓝 ((u : L2R))) ∧
      Tendsto (fun n => oscillatorCoreMap (g n)) atTop
        (𝓝 (harmonicOscillatorPMap.closure u)) := by
  have hcl : harmonicOscillatorPMap.IsClosable :=
    isClosable_of_isSymmetric harmonicOscillatorPMap_isSymmetric harmonicOscillatorPMap_dense
  obtain ⟨w, hw1, hw2⟩ := exists_seq_tendsto_closure hcl u
  choose g hg1 hg2 using fun n => exists_schwartz_of_mem_domain (w n)
  refine ⟨g, ?_, ?_⟩
  · simpa only [hg1] using hw1
  · simpa only [hg2] using hw2

/-- Domain elements with small norm and small image lie in the closure of the
good set. -/
theorem mem_closure_goodSet (u : (harmonicOscillatorPMap.closure).domain)
    (h1 : ‖(u : L2R)‖ ≤ 1) (h2 : ‖harmonicOscillatorPMap.closure u‖ ≤ 1) :
    (u : L2R) ∈ closure (goodSet 2) := by
  obtain ⟨g, hg1, hg2⟩ := exists_seq_schwartz_tendsto u
  -- the norms converge
  have hnorm : Tendsto (fun n => ‖schwartzToL2 (g n)‖) atTop (𝓝 ‖(u : L2R)‖) :=
    (continuous_norm.tendsto _).comp hg1
  -- the energies converge
  have hinner : Tendsto (fun n => inner ℂ (oscillatorCoreMap (g n)) (schwartzToL2 (g n)))
      atTop (𝓝 (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R)))) :=
    (continuous_inner (𝕜 := ℂ)).continuousAt.tendsto.comp (hg2.prodMk_nhds hg1)
  have henergy : Tendsto (fun n => energy (g n)) atTop
      (𝓝 (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R))).re) := by
    have h := (Complex.continuous_re.tendsto _).comp hinner
    simp only [Function.comp_def, inner_oscillatorCoreMap_self, Complex.ofReal_re] at h
    exact h
  -- the limits are at most one
  have hlim2 : (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R))).re ≤ 1 := by
    have hle : ‖inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R))‖
        ≤ ‖harmonicOscillatorPMap.closure u‖ * ‖(u : L2R)‖ := norm_inner_le_norm _ _
    have h3 : ‖harmonicOscillatorPMap.closure u‖ * ‖(u : L2R)‖ ≤ 1 := by
      have := norm_nonneg (u : L2R)
      have := norm_nonneg (harmonicOscillatorPMap.closure u)
      nlinarith
    have h4 := Complex.re_le_norm (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R)))
    linarith
  -- eventually the Schwartz approximants lie in the good set
  have hev : ∀ᶠ n in atTop, schwartzToL2 (g n) ∈ goodSet 2 := by
    have e1 : ∀ᶠ n in atTop, ‖schwartzToL2 (g n)‖ < 2 :=
      hnorm.eventually_lt_const (by linarith)
    have e2 : ∀ᶠ n in atTop, energy (g n) < 2 :=
      henergy.eventually_lt_const (by linarith)
    filter_upwards [e1, e2] with n hn1 hn2
    exact ⟨g n, rfl, hn1.le, hn2.le⟩
  exact mem_closure_of_tendsto hg1 hev

/-- The unit-shift resolvents map the closed unit ball into the closure of the
good set. -/
theorem resolvent_mem_closure_goodSet {z : ℂ} (hz : |z.im| = 1) (hz' : z.re = 0)
    {R : L2R →L[ℂ] L2R} (hR : RightResolvent harmonicOscillatorPMap.closure z R)
    (hsym : IsSymmetric harmonicOscillatorPMap.closure)
    (y : L2R) (hy : ‖y‖ ≤ 1) : R y ∈ closure (goodSet 2) := by
  obtain ⟨hmem, hval⟩ := hR y
  set v : (harmonicOscillatorPMap.closure).domain := ⟨R y, hmem⟩ with hv
  have hznorm : ‖z‖ = 1 := by
    have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
    have him : z.im ^ 2 = 1 := by
      have := hz
      nlinarith [abs_nonneg z.im, sq_abs z.im]
    have h0 : ‖z‖ ^ 2 = 1 := by rw [this, hz', him]; ring
    nlinarith [norm_nonneg z]
  -- the norm bound on `v`
  have hvnorm : ‖(v : L2R)‖ ≤ 1 := by
    have h := norm_le_norm_shifted hsym hz v
    rw [hval] at h
    linarith
  -- the Pythagorean identity
  have hTnorm : ‖harmonicOscillatorPMap.closure v‖ ≤ 1 := by
    have hre : (inner ℂ (harmonicOscillatorPMap.closure v) ((v : L2R))).im = 0 :=
      hsym.inner_self_im v
    have hexp := norm_sub_sq (𝕜 := ℂ) (harmonicOscillatorPMap.closure v) (z • (v : L2R))
    rw [inner_smul_right, norm_smul, hznorm] at hexp
    have hcross : RCLike.re (z * inner ℂ (harmonicOscillatorPMap.closure v) ((v : L2R))) = 0 := by
      show (z * inner ℂ (harmonicOscillatorPMap.closure v) ((v : L2R))).re = 0
      rw [Complex.mul_re, hre, hz']
      ring
    rw [hcross, hval] at hexp
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
    have hnn := norm_nonneg (harmonicOscillatorPMap.closure v)
    nlinarith [norm_nonneg (v : L2R)]
  have := mem_closure_goodSet v hvnorm hTnorm
  simpa [hv] using this

/-- **Compactness of a unit-shift resolvent of the oscillator closure.** -/
theorem isCompactOperator_of_rightResolvent {z : ℂ} (hz : |z.im| = 1) (hz' : z.re = 0)
    {R : L2R →L[ℂ] L2R} (hR : RightResolvent harmonicOscillatorPMap.closure z R)
    (hsym : IsSymmetric harmonicOscillatorPMap.closure) :
    IsCompactOperator R := by
  refine isCompactOperator_of_approx R fun ε hε => ?_
  obtain ⟨V, hVfin, hV⟩ := exists_finiteDimensional_approx 2 (ε / 2) (by linarith)
  refine ⟨V, hVfin, fun y hy => ?_⟩
  obtain ⟨v, hvV, hv⟩ :=
    exists_approx_of_mem_closure (C := 2) (by linarith : (0:ℝ) < ε / 2) hV
      (resolvent_mem_closure_goodSet hz hz' hR hsym y hy)
  exact ⟨v, hvV, by linarith [hv]⟩

end Brockian.Weyl.OscillatorCompact

/-
  ClosureResolvent.lean — reconstruction of the corpus modules

  * `Brockian/WeylKatoResolventPackage.lean` (the `RightResolvent` predicate and
    the `ResolventAtI` package),
  * `Brockian/WeylWeightedRellich.lean`      (verbatim),
  * `Brockian/WeylClosedShiftedRanges.lean`  (the construction
    `closureResolventAtIOfEssentiallySelfAdjoint` of the two canonical
    unit-shift resolvents of the closure of an essentially self-adjoint
    symmetric operator).
-/
import RequestProject.Base

open scoped InnerProductSpace

namespace Brockian.Weyl.KatoRellichScaffold

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Right resolvent.** `R` is a bounded right inverse of `T - z`: every `x`
is mapped into the domain of `T` and `(T - z) (R x) = x`. -/
def RightResolvent (T : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  ∀ x : H, ∃ h : R x ∈ T.domain, T ⟨R x, h⟩ - z • R x = x

end Brockian.Weyl.KatoRellichScaffold

namespace Brockian.Weyl.KatoResolventPackage

open Brockian.Weyl.KatoRellichScaffold

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded right resolvents for `T+i` and `T-i`, with the Hilbert-space
self-adjoint resolvent bound normalized at distance one from the real axis. -/
structure ResolventAtI (T : H →ₗ.[ℂ] H) where
  Radd : H →L[ℂ] H
  Rsub : H →L[ℂ] H
  right_add : RightResolvent T (-Complex.I) Radd
  right_sub : RightResolvent T Complex.I Rsub
  norm_add : ‖Radd‖ ≤ 1
  norm_sub : ‖Rsub‖ ≤ 1

end Brockian.Weyl.KatoResolventPackage

/-! ## Brockian/WeylWeightedRellich.lean -/

namespace Brockian.Weyl.WeightedRellich

open Brockian.Weyl.KatoResolventPackage

variable {H E Eadd Esub : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Eadd] [NormedSpace ℂ Eadd]
  [NormedAddCommGroup Esub] [NormedSpace ℂ Esub]

/-- A resolvent factorization through a compactly embedded weighted space. -/
structure Factorization (R : H →L[ℂ] H) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] where
  embedding : E →L[ℂ] H
  lift : H →L[ℂ] E
  compact_embedding : IsCompactOperator embedding
  factorization : embedding.comp lift = R

omit [CompleteSpace H] in
/-- The compact-embedding factorization makes the resolvent compact. -/
theorem Factorization.isCompactOperator {R : H →L[ℂ] H}
    (F : Factorization R E) : IsCompactOperator R := by
  change IsCompactOperator (fun x : H => R x)
  have heq : (fun x : H => F.embedding (F.lift x)) = fun x : H => R x := by
    funext x
    exact congrArg (fun A : H →L[ℂ] H => A x) F.factorization
  rw [← heq]
  exact F.compact_embedding.comp_clm F.lift

omit [CompleteSpace H] in
/-- Compactness gives compact closure of the image of every closed ball. -/
theorem Factorization.isCompact_closure_image_closedBall {R : H →L[ℂ] H}
    (F : Factorization R E) (r : ℝ) :
    IsCompact (closure (R '' Metric.closedBall 0 r)) :=
  F.isCompactOperator.isCompact_closure_image_closedBall r

/-- The factorization interface is exact. -/
noncomputable def Factorization.ofCompact (R : H →L[ℂ] H)
    (hR : IsCompactOperator R) : Factorization R H where
  embedding := R
  lift := ContinuousLinearMap.id ℂ H
  compact_embedding := hR
  factorization := by ext x; rfl

omit [CompleteSpace H] in
/-- Both unit-shift resolvents are compact once each has a weighted-Rellich
factorization. -/
theorem compact_resolvents_of_factorizations {T : H →ₗ.[ℂ] H}
    (hres : ResolventAtI T)
    (Fadd : Factorization hres.Radd Eadd)
    (Fsub : Factorization hres.Rsub Esub) :
    IsCompactOperator hres.Radd ∧ IsCompactOperator hres.Rsub :=
  ⟨Fadd.isCompactOperator, Fsub.isCompactOperator⟩

end Brockian.Weyl.WeightedRellich

/-! ## Brockian/WeylClosedShiftedRanges.lean (reconstruction) -/

namespace Brockian.Weyl.ClosedShiftedRanges

open Brockian.Weyl.Operator
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoResolventPackage
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range of the shifted operator `T - z`. -/
def shiftedRange (T : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  LinearMap.range (T.toFun - z • T.domain.subtype)

omit [CompleteSpace H] in
theorem mem_shiftedRange_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (y : H) :
    y ∈ shiftedRange T z ↔ ∃ v : T.domain, T v - z • (v : H) = y := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩

/-! ### Closability and symmetry of the closure -/

/-- A densely defined symmetric operator is contained in its adjoint. -/
theorem le_adjoint_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : T ≤ T.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint hd hsym

/-- A densely defined symmetric operator is closable. -/
theorem isClosable_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : T.IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨T.adjoint, LinearPMap.adjoint_isClosed hd, le_adjoint_of_isSymmetric hsym hd⟩

omit [CompleteSpace H] in
/-- A closed operator equals its own closure. -/
theorem closure_eq_self_of_isClosed {T : H →ₗ.[ℂ] H} (h : T.IsClosed) :
    T.closure = T := by
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← h.isClosable.graph_closure_eq_closure_graph]
  exact (h.submodule_topologicalClosure_eq)

/-- The closure of a densely defined symmetric operator is contained in the
adjoint. -/
theorem closure_le_adjoint {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : T.closure ≤ T.adjoint := by
  have hcl : (T.adjoint).IsClosed := LinearPMap.adjoint_isClosed hd
  have h := hcl.isClosable.closure_mono (le_adjoint_of_isSymmetric hsym hd)
  rwa [closure_eq_self_of_isClosed hcl] at h

omit [CompleteSpace H] in
/-- Every element of the domain of the closure is a graph limit of elements of
the domain. -/
theorem exists_seq_tendsto_closure {T : H →ₗ.[ℂ] H} (hcl : T.IsClosable)
    (x : T.closure.domain) :
    ∃ u : ℕ → T.domain, Tendsto (fun n => ((u n : H))) atTop (𝓝 (x : H)) ∧
      Tendsto (fun n => T (u n)) atTop (𝓝 (T.closure x)) := by
  have hmem : ((x : H), T.closure x) ∈ T.closure.graph := T.closure.mem_graph x
  rw [← hcl.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe] at hmem
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose v hv1 hv2 using fun n => (LinearPMap.mem_graph_iff T).mp (hw n)
  refine ⟨v, ?_, ?_⟩
  · have h := (continuous_fst.tendsto ((x : H), T.closure x)).comp hlim
    simpa [Function.comp_def, hv1] using h
  · have h := (continuous_snd.tendsto ((x : H), T.closure x)).comp hlim
    simpa [Function.comp_def, hv2] using h

/-- The closure of a densely defined symmetric operator is symmetric. -/
theorem isSymmetric_closure {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : IsSymmetric T.closure := by
  have hcl := isClosable_of_isSymmetric hsym hd
  have hle := closure_le_adjoint hsym hd
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := T) hd
  intro x y
  obtain ⟨u, hu1, hu2⟩ := exists_seq_tendsto_closure hcl y
  have hx : (x : H) ∈ T.adjoint.domain := hle.1 x.2
  have hxval : T.closure x = T.adjoint ⟨(x : H), hx⟩ := hle.2 rfl
  have hkey : ∀ n, ⟪T.closure x, ((u n : H))⟫_ℂ = ⟪(x : H), T (u n)⟫_ℂ := by
    intro n
    rw [hxval]
    exact hfa ⟨(x : H), hx⟩ (u n)
  have hlim1 : Tendsto (fun n => ⟪T.closure x, ((u n : H))⟫_ℂ) atTop
      (𝓝 ⟪T.closure x, (y : H)⟫_ℂ) :=
    (continuous_inner (𝕜 := ℂ)).continuousAt.tendsto.comp
      (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hu1)
  have hlim2 : Tendsto (fun n => ⟪(x : H), T (u n)⟫_ℂ) atTop
      (𝓝 ⟪(x : H), T.closure y⟫_ℂ) :=
    (continuous_inner (𝕜 := ℂ)).continuousAt.tendsto.comp
      (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hu2)
  have hlim3 : Tendsto (fun n => ⟪T.closure x, ((u n : H))⟫_ℂ) atTop
      (𝓝 ⟪(x : H), T.closure y⟫_ℂ) := by
    simpa only [hkey] using hlim2
  exact tendsto_nhds_unique hlim1 hlim3

/-! ### Orthogonality of the shifted range and the deficiency spaces -/

/-- If `g` is orthogonal to the range of `T - z`, then `g` lies in the
deficiency space of `T` at `conj z`. -/
theorem mem_deficiencySpace_of_mem_orthogonal {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) {z : ℂ} {g : H}
    (hg : g ∈ (shiftedRange T z)ᗮ) :
    ∃ hmem : g ∈ T.adjoint.domain,
      (⟨g, hmem⟩ : T.adjoint.domain) ∈ deficiencySpace T ((starRingEnd ℂ) z) := by
  have hzero : ∀ v : T.domain, ⟪T v - z • (v : H), g⟫_ℂ = 0 := fun v =>
    hg _ ((mem_shiftedRange_iff T z _).mpr ⟨v, rfl⟩)
  have hkey : ∀ v : T.domain, ⟪(starRingEnd ℂ) z • g, (v : H)⟫_ℂ = ⟪g, T v⟫_ℂ := by
    intro v
    have h := hzero v
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h
    have h2 : ⟪g, T v⟫_ℂ = z * ⟪g, (v : H)⟫_ℂ := by
      have hc := congrArg (starRingEnd ℂ) h
      rwa [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc
    rw [inner_smul_left, Complex.conj_conj, h2]
  have hmem : g ∈ T.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨(starRingEnd ℂ) z • g, hkey⟩
  refine ⟨hmem, ?_⟩
  rw [mem_deficiencySpace_iff]
  exact LinearPMap.adjoint_apply_eq hd ⟨g, hmem⟩ hkey

/-! ### Injectivity and surjectivity of the shifted closure -/

omit [CompleteSpace H] in
/-- The basic lower bound for a symmetric operator at a spectral parameter at
distance one from the real axis. -/
theorem norm_le_norm_shifted {S : H →ₗ.[ℂ] H} (hS : IsSymmetric S) {z : ℂ}
    (hz : |z.im| = 1) (v : S.domain) : ‖(v : H)‖ ≤ ‖S v - z • (v : H)‖ := by
  have h := hS.norm_sub_smul_ge v z
  rwa [hz, one_mul] at h

omit [CompleteSpace H] in
/-- The shifted operator is injective. -/
theorem eq_of_shifted_eq {S : H →ₗ.[ℂ] H} (hS : IsSymmetric S) {z : ℂ}
    (hz : |z.im| = 1) {v w : S.domain}
    (h : S v - z • (v : H) = S w - z • (w : H)) : v = w := by
  have hvw : S (v - w) - z • ((v - w : S.domain) : H) = 0 := by
    have hmap : S (v - w) = S v - S w := LinearPMap.map_sub _ _ _
    have hcoe : ((v - w : S.domain) : H) = (v : H) - (w : H) := rfl
    rw [hmap, hcoe, smul_sub, sub_sub_sub_comm, h, sub_self]
  have hnorm := norm_le_norm_shifted hS hz (v - w)
  rw [hvw, norm_zero] at hnorm
  have h0 : ((v - w : S.domain) : H) = 0 := norm_le_zero_iff.mp hnorm
  exact sub_eq_zero.mp (Subtype.ext h0)

/-- The shifted range of the closure is closed. -/
theorem isClosed_shiftedRange_closure {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) {z : ℂ} (hz : |z.im| = 1) :
    IsClosed ((shiftedRange T.closure z : Submodule ℂ H) : Set H) := by
  have hcl := isClosable_of_isSymmetric hsym hd
  have hclosed : T.closure.IsClosed := hcl.closure_isClosed
  have hsymc := isSymmetric_closure hsym hd
  rw [← isSeqClosed_iff_isClosed]
  intro y ylim hy hlim
  choose v hv using fun n => (mem_shiftedRange_iff T.closure z (y n)).mp (hy n)
  have hbound : ∀ m n : ℕ, ‖(v m : H) - (v n : H)‖ ≤ ‖y m - y n‖ := by
    intro m n
    have h := norm_le_norm_shifted hsymc hz (v m - v n)
    have hcoe : ((v m - v n : T.closure.domain) : H) = (v m : H) - (v n : H) := rfl
    have hmap : T.closure (v m - v n) = T.closure (v m) - T.closure (v n) :=
      LinearPMap.map_sub _ _ _
    rw [hcoe, hmap] at h
    have hexp : T.closure (v m) - T.closure (v n) - z • ((v m : H) - (v n : H))
        = y m - y n := by
      rw [smul_sub, ← hv m, ← hv n]; abel
    rwa [hexp] at h
  -- `v` is Cauchy, hence converges
  have hyc : CauchySeq y := hlim.cauchySeq
  have hvc : CauchySeq (fun n => (v n : H)) := by
    rw [Metric.cauchySeq_iff] at hyc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hyc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have := hbound m n
    rw [dist_eq_norm]
    calc ‖(v m : H) - (v n : H)‖ ≤ ‖y m - y n‖ := this
      _ = dist (y m) (y n) := (dist_eq_norm _ _).symm
      _ < ε := hN m hm n hn
  obtain ⟨vlim, hvlim⟩ := cauchySeq_tendsto_of_complete hvc
  -- the images converge too
  have hTv : Tendsto (fun n => T.closure (v n)) atTop (𝓝 (ylim + z • vlim)) := by
    have h1 : ∀ n, T.closure (v n) = y n + z • (v n : H) := by
      intro n; rw [← hv n]; abel
    have h2 : Tendsto (fun n => y n + z • (v n : H)) atTop (𝓝 (ylim + z • vlim)) :=
      hlim.add ((hvlim.const_smul z))
    simpa only [h1] using h2
  -- the graph is closed, so the limit is in the domain
  have hgraph : ((vlim : H), ylim + z • vlim) ∈ T.closure.graph := by
    have hmem : ∀ n, ((v n : H), T.closure (v n)) ∈ T.closure.graph :=
      fun n => T.closure.mem_graph (v n)
    have hlimprod : Tendsto (fun n => ((v n : H), T.closure (v n))) atTop
        (𝓝 ((vlim : H), ylim + z • vlim)) := hvlim.prodMk_nhds hTv
    exact hclosed.mem_of_tendsto hlimprod (Filter.Eventually.of_forall hmem)
  obtain ⟨w, hw1, hw2⟩ := (LinearPMap.mem_graph_iff T.closure).mp hgraph
  refine (mem_shiftedRange_iff T.closure z ylim).mpr ⟨w, ?_⟩
  rw [hw2, hw1]
  simp

/-- Both shifted ranges of the closure are everything, under essential
self-adjointness. -/
theorem shiftedRange_closure_eq_top {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) {z : ℂ}
    (hz : |z.im| = 1) (hdef : deficiencySpace T ((starRingEnd ℂ) z) = ⊥) :
    shiftedRange T.closure z = ⊤ := by
  have hclosedset := isClosed_shiftedRange_closure hsym hd hz
  haveI : CompleteSpace (shiftedRange T.closure z) :=
    hclosedset.completeSpace_coe
  have horth : (shiftedRange T.closure z)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    -- `g` is orthogonal to the smaller range of `T` itself
    have hsub : shiftedRange T z ≤ shiftedRange T.closure z := by
      intro y hy
      obtain ⟨v, hv⟩ := (mem_shiftedRange_iff T z y).mp hy
      have hmemw : (v : H) ∈ T.closure.domain := (T.le_closure).1 v.2
      have hval : T v = T.closure ⟨(v : H), hmemw⟩ := (T.le_closure).2 rfl
      exact (mem_shiftedRange_iff T.closure z y).mpr
        ⟨⟨(v : H), hmemw⟩, by rw [← hval]; exact hv⟩
    have hg' : g ∈ (shiftedRange T z)ᗮ := by
      intro u hu
      exact hg u (hsub hu)
    obtain ⟨hmem, hdefmem⟩ := mem_deficiencySpace_of_mem_orthogonal hd hg'
    rw [hdef, Submodule.mem_bot] at hdefmem
    exact congrArg Subtype.val hdefmem
  exact (Submodule.orthogonal_eq_bot_iff).mp horth

/-- Essential self-adjointness makes the shifted closure surjective. -/
theorem exists_shifted_eq {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) {z : ℂ}
    (hz : |z.im| = 1) (hdef : deficiencySpace T ((starRingEnd ℂ) z) = ⊥) (y : H) :
    ∃ v : T.closure.domain, T.closure v - z • (v : H) = y := by
  have h := shiftedRange_closure_eq_top hsym hd hz hdef
  have : y ∈ shiftedRange T.closure z := by rw [h]; trivial
  exact (mem_shiftedRange_iff T.closure z y).mp this

/-! ### The bounded inverse -/

/-- The bounded inverse of `S - z` for a symmetric `S`, given surjectivity. -/
noncomputable def shiftedInverse (S : H →ₗ.[ℂ] H) (z : ℂ) (hS : IsSymmetric S)
    (hz : |z.im| = 1) (hsurj : ∀ y : H, ∃ v : S.domain, S v - z • (v : H) = y) :
    H →L[ℂ] H := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun y => (((hsurj y).choose : S.domain) : H)
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro y₁ y₂
    have h1 := (hsurj y₁).choose_spec
    have h2 := (hsurj y₂).choose_spec
    have h3 := (hsurj (y₁ + y₂)).choose_spec
    have heq : (hsurj (y₁ + y₂)).choose = (hsurj y₁).choose + (hsurj y₂).choose := by
      refine eq_of_shifted_eq hS hz ?_
      have hcoe : (((hsurj y₁).choose + (hsurj y₂).choose : S.domain) : H)
          = ((hsurj y₁).choose : H) + ((hsurj y₂).choose : H) := rfl
      have hR : S ((hsurj y₁).choose + (hsurj y₂).choose)
            - z • (((hsurj y₁).choose + (hsurj y₂).choose : S.domain) : H) = y₁ + y₂ := by
        rw [LinearPMap.map_add, hcoe, smul_add]
        have hsplit : S (hsurj y₁).choose + S (hsurj y₂).choose
            - (z • ((hsurj y₁).choose : H) + z • ((hsurj y₂).choose : H))
            = (S (hsurj y₁).choose - z • ((hsurj y₁).choose : H))
              + (S (hsurj y₂).choose - z • ((hsurj y₂).choose : H)) := by abel
        rw [hsplit, h1, h2]
      rw [h3, hR]
    rw [heq]; rfl
  · intro c y
    have h1 := (hsurj y).choose_spec
    have h2 := (hsurj (c • y)).choose_spec
    have heq : (hsurj (c • y)).choose = c • (hsurj y).choose := by
      refine eq_of_shifted_eq hS hz ?_
      have hcoe : ((c • (hsurj y).choose : S.domain) : H) = c • ((hsurj y).choose : H) := rfl
      have hR : S (c • (hsurj y).choose) - z • ((c • (hsurj y).choose : S.domain) : H)
          = c • y := by
        rw [LinearPMap.map_smul, hcoe, smul_comm z c, ← smul_sub, h1]
      rw [h2, hR]
    rw [heq]; rfl
  · intro y
    have h1 := (hsurj y).choose_spec
    have h := norm_le_norm_shifted hS hz (hsurj y).choose
    rw [h1] at h
    simpa using h

omit [CompleteSpace H] in
theorem shiftedInverse_spec (S : H →ₗ.[ℂ] H) (z : ℂ) (hS : IsSymmetric S)
    (hz : |z.im| = 1) (hsurj : ∀ y : H, ∃ v : S.domain, S v - z • (v : H) = y) :
    RightResolvent S z (shiftedInverse S z hS hz hsurj) := by
  intro x
  have h1 := (hsurj x).choose_spec
  have hmem : (shiftedInverse S z hS hz hsurj) x ∈ S.domain := ((hsurj x).choose).2
  refine ⟨hmem, ?_⟩
  have : (⟨(shiftedInverse S z hS hz hsurj) x, hmem⟩ : S.domain) = (hsurj x).choose :=
    Subtype.ext rfl
  rw [this]
  exact h1

omit [CompleteSpace H] in
theorem norm_shiftedInverse_le (S : H →ₗ.[ℂ] H) (z : ℂ) (hS : IsSymmetric S)
    (hz : |z.im| = 1) (hsurj : ∀ y : H, ∃ v : S.domain, S v - z • (v : H) = y) :
    ‖shiftedInverse S z hS hz hsurj‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **The canonical unit-shift resolvents of the closure of an essentially
self-adjoint symmetric operator.** -/
noncomputable def closureResolventAtIOfEssentiallySelfAdjoint {T : H →ₗ.[ℂ] H}
    (hsym : IsSymmetric T) (hd : Dense (T.domain : Set H))
    (hESA : EssentiallySelfAdjoint T) : ResolventAtI T.closure := by
  have hsymc := isSymmetric_closure hsym hd
  have hzadd : |(-Complex.I).im| = 1 := by simp
  have hzsub : |(Complex.I).im| = 1 := by simp
  have hdefadd : deficiencySpace T ((starRingEnd ℂ) (-Complex.I)) = ⊥ := by
    simpa using hESA.1
  have hdefsub : deficiencySpace T ((starRingEnd ℂ) (Complex.I)) = ⊥ := by
    simpa using hESA.2
  exact
    { Radd := shiftedInverse T.closure (-Complex.I) hsymc hzadd
        (exists_shifted_eq hsym hd hzadd hdefadd)
      Rsub := shiftedInverse T.closure Complex.I hsymc hzsub
        (exists_shifted_eq hsym hd hzsub hdefsub)
      right_add := shiftedInverse_spec _ _ _ _ _
      right_sub := shiftedInverse_spec _ _ _ _ _
      norm_add := norm_shiftedInverse_le _ _ _ _ _
      norm_sub := norm_shiftedInverse_le _ _ _ _ _ }

end Brockian.Weyl.ClosedShiftedRanges

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

/-
  Rellich.lean — the concrete weighted-Rellich estimate.

  A family of Schwartz functions with `∫ ‖g'‖² + ∫ x²‖g‖² ≤ C` is, in `L²(ℝ)`,
  uniformly close to a *fixed* finite-dimensional space of step functions:

  * the confining weight `x²` controls the mass outside `[-R, R]`;
  * the kinetic term `∫ ‖g'‖²` controls the oscillation of `g` inside each cell
    of a partition of `(-R, R]` into `n` intervals of length `h`.

  Together these give `‖g - s‖²_{L²} ≤ h² ∫‖g'‖² + R⁻² ∫ x²‖g‖²`, where `s` is
  the step function taking on each cell the value of `g` at the right endpoint
  of that cell.  Choosing `R` large and `h` small makes the right-hand side as
  small as desired, uniformly over the family.
-/
import RequestProject.Base

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.Rellich

open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.HarmonicOscillator

/-! ### Cauchy–Schwarz for a set integral -/

/-- **Cauchy–Schwarz.** `(∫_I f)² ≤ |I| · ∫_I f²`. -/
theorem sq_setIntegral_le {I : Set ℝ} (f : ℝ → ℝ)
    (hf : IntegrableOn f I) (hf2 : IntegrableOn (fun x => f x ^ 2) I)
    (hfin : volume I ≠ ⊤) :
    (∫ x in I, f x) ^ 2 ≤ (volume.real I) * ∫ x in I, f x ^ 2 := by
  set m := volume.real I with hm
  have hm0 : 0 ≤ m := by positivity
  rcases eq_or_lt_of_le hm0 with hmz | hmpos
  · have hz : volume I = 0 := by
      have h : (volume I).toReal = 0 := hmz.symm
      exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hfin
    have h1 : ∫ x in I, f x = 0 := by
      rw [Measure.restrict_eq_zero.mpr hz]; simp
    have h2 : ∫ x in I, f x ^ 2 = 0 := by
      rw [Measure.restrict_eq_zero.mpr hz]; simp
    rw [h1, h2]; simp
  · set t := (∫ x in I, f x) / m with ht
    have hconst : IntegrableOn (fun _ : ℝ => t ^ 2) I := integrableOn_const hfin
    have hlin : IntegrableOn (fun x => f x ^ 2 - 2 * t * f x) I :=
      hf2.sub (hf.const_mul (2 * t))
    have hkey : 0 ≤ ∫ x in I, (f x - t) ^ 2 := by
      apply integral_nonneg; intro x; positivity
    have hexp : ∫ x in I, (f x - t) ^ 2
        = (∫ x in I, f x ^ 2) - 2 * t * (∫ x in I, f x) + t ^ 2 * m := by
      have hpt : ∀ x, (f x - t) ^ 2 = (f x ^ 2 - (2 * t) * f x) + t ^ 2 := by intro x; ring
      simp only [hpt]
      rw [integral_add hlin hconst, integral_sub hf2 (hf.const_mul (2 * t)),
        integral_const_mul]
      simp [hm, mul_comm]
    rw [hexp] at hkey
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have htm : t * m = ∫ x in I, f x := div_mul_cancel₀ _ hmne
    nlinarith [hkey, htm]

/-! ### The one-dimensional Poincaré estimate on a cell -/

/-- The derivative of a Schwartz function is continuous. -/
theorem deriv_continuous (g : SchwartzMap ℝ ℂ) : Continuous (deriv (g : ℝ → ℂ)) := by
  have h : deriv (g : ℝ → ℂ) = ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  rw [h]; exact (SchwartzMap.derivCLM ℂ ℂ g).continuous

/-- **The fundamental gradient estimate.** `‖g x − g y‖² ≤ (x−y) ∫_y^x ‖g'‖²`. -/
theorem norm_sub_sq_le (g : SchwartzMap ℝ ℂ) {y x : ℝ} (hyx : y ≤ x) :
    ‖g x - g y‖ ^ 2 ≤ (x - y) * ∫ t in Set.Ioc y x, ‖deriv (g : ℝ → ℂ) t‖ ^ 2 := by
  have hc := deriv_continuous g
  have hftc : ∫ t in y..x, deriv (g : ℝ → ℂ) t = g x - g y := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => ?_)
      (hc.intervalIntegrable _ _)
    exact (g.differentiable.differentiableAt (x := t)).hasDerivAt
  have h1 : ‖g x - g y‖ ≤ ∫ t in y..x, ‖deriv (g : ℝ → ℂ) t‖ := by
    rw [← hftc]; exact intervalIntegral.norm_integral_le_integral_norm hyx
  rw [intervalIntegral.integral_of_le hyx] at h1
  have hm : (volume (Set.Ioc y x)).toReal = x - y := by
    simp [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ x - y)]
  have hcs := sq_setIntegral_le (I := Set.Ioc y x) (fun t => ‖deriv (g : ℝ → ℂ) t‖)
    hc.norm.integrableOn_Ioc (by simpa using (hc.norm.pow 2).integrableOn_Ioc)
    (by simp [Real.volume_Ioc])
  rw [Measure.real, hm] at hcs
  have h0 : (0:ℝ) ≤ ∫ t in Set.Ioc y x, ‖deriv (g : ℝ → ℂ) t‖ :=
    integral_nonneg fun _ => norm_nonneg _
  nlinarith [norm_nonneg (g x - g y), h1, hcs]

/-- **Cell estimate.** On an interval of length `b − a`, replacing `g` by its
value at the right endpoint costs at most `(b−a)² ∫ ‖g'‖²`. -/
theorem cell_estimate (g : SchwartzMap ℝ ℂ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, ‖g x - g b‖ ^ 2
      ≤ (b - a) ^ 2 * ∫ x in Set.Ioc a b, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
  have hc := deriv_continuous g
  set K : ℝ := ∫ x in Set.Ioc a b, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 with hK
  have hint2 : IntegrableOn (fun x => ‖deriv (g : ℝ → ℂ) x‖ ^ 2) (Set.Ioc a b) := by
    simpa using (hc.norm.pow 2).integrableOn_Ioc
  have hbound : ∀ x ∈ Set.Ioc a b, ‖g x - g b‖ ^ 2 ≤ (b - a) * K := by
    intro x hx
    have hxb : x ≤ b := hx.2
    have hax : a ≤ x := le_of_lt hx.1
    have h1 := norm_sub_sq_le g hxb
    rw [← norm_neg, neg_sub] at h1
    set J : ℝ := ∫ t in Set.Ioc x b, ‖deriv (g : ℝ → ℂ) t‖ ^ 2 with hJ
    have hsub : J ≤ K := by
      refine setIntegral_mono_set hint2 ?_ ?_
      · exact Filter.Eventually.of_forall fun _ => by positivity
      · exact Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_left hax)
    have hJ0 : 0 ≤ J := integral_nonneg fun _ => by positivity
    nlinarith [h1, hsub, hJ0, hxb, hax]
  have hintL : IntegrableOn (fun x => ‖g x - g b‖ ^ 2) (Set.Ioc a b) :=
    ((g.continuous.sub continuous_const).norm.pow 2).integrableOn_Ioc
  have hmono := setIntegral_mono_on hintL (integrableOn_const (by simp [Real.volume_Ioc]))
    measurableSet_Ioc hbound
  rw [setIntegral_const] at hmono
  have hm : (volume.real (Set.Ioc a b)) = b - a := by
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]
  rw [hm, smul_eq_mul] at hmono
  calc ∫ x in Set.Ioc a b, ‖g x - g b‖ ^ 2 ≤ (b - a) * ((b - a) * K) := hmono
    _ = (b - a) ^ 2 * K := by ring

/-! ### Cells, step functions, and their `L²` classes -/

/-- The `j`-th cell of the partition of `(-R, -R + n·h]` into intervals of
length `h`. -/
def cellSet (Rr hh : ℝ) (j : ℕ) : Set ℝ := Set.Ioc (-Rr + j * hh) (-Rr + (j + 1) * hh)

theorem cells_disjoint (Rr hh : ℝ) (hh0 : 0 < hh) :
    Pairwise (Function.onFun Disjoint (cellSet Rr hh)) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (cellSet Rr hh i) (cellSet Rr hh j) := by
    intro i j hij
    apply Set.Ioc_disjoint_Ioc.mpr
    have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have h1 : -Rr + ((i : ℝ) + 1) * hh ≤ -Rr + j * hh := by nlinarith
    calc min (-Rr + ((i : ℝ) + 1) * hh) (-Rr + ((j : ℝ) + 1) * hh)
        ≤ -Rr + ((i : ℝ) + 1) * hh := min_le_left _ _
      _ ≤ -Rr + (j : ℝ) * hh := h1
      _ ≤ max (-Rr + (i : ℝ) * hh) (-Rr + (j : ℝ) * hh) := le_max_right _ _
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem cells_union (Rr hh : ℝ) (hh0 : 0 ≤ hh) : ∀ n : ℕ,
    (⋃ j ∈ Finset.range n, cellSet Rr hh j) = Set.Ioc (-Rr) (-Rr + n * hh) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.range_add_one, Finset.set_biUnion_insert, ih, Set.union_comm, cellSet]
      rw [Set.Ioc_union_Ioc_eq_Ioc (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
        (by nlinarith)]
      congr 1
      push_cast
      ring

/-- The pointwise step function with value `c j` on the `j`-th cell. -/
noncomputable def stepVal (c : ℕ → ℂ) (Rr hh : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, Set.indicator (cellSet Rr hh j) (fun _ => c j) x

theorem stepVal_of_mem (c : ℕ → ℂ) {Rr hh : ℝ} (hh0 : 0 < hh) {n k : ℕ} (hk : k < n)
    {x : ℝ} (hx : x ∈ cellSet Rr hh k) : stepVal c Rr hh n x = c k := by
  rw [stepVal, Finset.sum_eq_single k]
  · rw [Set.indicator_of_mem hx]
  · intro j _ hjk
    exact Set.indicator_of_notMem
      (fun hxj => (cells_disjoint Rr hh hh0 hjk).le_bot ⟨hxj, hx⟩) _
  · intro hkn; exact absurd (Finset.mem_range.mpr hk) hkn

theorem stepVal_of_notMem (c : ℕ → ℂ) {Rr hh : ℝ} (hh0 : 0 ≤ hh) {n : ℕ}
    {x : ℝ} (hx : x ∉ Set.Ioc (-Rr) (-Rr + n * hh)) : stepVal c Rr hh n x = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  refine Set.indicator_of_notMem (fun hxj => hx ?_) _
  rw [← cells_union Rr hh hh0 n]
  exact Set.mem_biUnion hj hxj

/-- The `L²` class of the indicator of the `j`-th cell. -/
noncomputable def cellLp (Rr hh : ℝ) (j : ℕ) : L2R :=
  indicatorConstLp 2 (measurableSet_Ioc (a := -Rr + j * hh) (b := -Rr + (j + 1) * hh))
    measure_Ioc_lt_top.ne (1 : ℂ)

/-- The `L²` class of the step function with values `c j`. -/
noncomputable def stepLp (c : ℕ → ℂ) (Rr hh : ℝ) (n : ℕ) : L2R :=
  ∑ j ∈ Finset.range n, c j • cellLp Rr hh j

theorem coeFn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → L2R) :
    ⇑(∑ i ∈ s, F i) =ᵐ[volume] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
  | insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
      show (⇑(∑ i ∈ insert a s, F i)) x = _
      rw [Finset.sum_insert ha, Finset.sum_insert ha, h1]
      simp only [Pi.add_apply, h2]

theorem stepLp_coeFn (c : ℕ → ℂ) (Rr hh : ℝ) (n : ℕ) :
    ⇑(stepLp c Rr hh n) =ᵐ[volume] stepVal c Rr hh n := by
  have hj : ∀ᵐ x : ℝ, ∀ j : ℕ,
      (c j • cellLp Rr hh j) x = Set.indicator (cellSet Rr hh j) (fun _ => c j) x := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (c j) (cellLp Rr hh j),
      indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (hs := measurableSet_Ioc (a := -Rr + j * hh) (b := -Rr + (j + 1) * hh))
        (hμs := measure_Ioc_lt_top.ne) (c := (1 : ℂ))] with x h1 h2
    rw [h1]
    simp only [Pi.smul_apply, cellLp]
    rw [h2]
    by_cases hx : x ∈ cellSet Rr hh j
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (s := Set.Ioc (-Rr + j * hh) (-Rr + (j + 1) * hh)) hx]
      simp
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (s := Set.Ioc (-Rr + j * hh) (-Rr + (j + 1) * hh)) hx]
      simp
  filter_upwards [coeFn_finset_sum (Finset.range n) (fun j => c j • cellLp Rr hh j), hj]
    with x h1 h2
  rw [stepLp, h1, stepVal]
  exact Finset.sum_congr rfl fun j _ => h2 j

/-! ### `L²` norms as integrals, and the integrability facts we need -/

theorem norm_sq_eq_integral (w : L2R) : ‖w‖ ^ 2 = ∫ x : ℝ, ‖w x‖ ^ 2 := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) w w
  have h2 : (inner ℂ w w : ℂ) = ((∫ x : ℝ, ‖w x‖ ^ 2 : ℝ) : ℂ) := by
    rw [h, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [RCLike.inner_apply]
    rw [mul_comm, RCLike.conj_mul]
    norm_cast
  have h3 : RCLike.re (inner ℂ w w : ℂ) = ‖w‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) w
  rw [h2] at h3
  simpa using h3.symm

theorem schwartz_norm_mul_integrable (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) volume := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  refine Integrable.bdd_mul (c := C) g.integrable.norm
    f.continuous.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  simpa using hC x

theorem integrable_deriv_sq (g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖deriv (g : ℝ → ℂ) x‖ ^ 2) volume := by
  have hd : deriv (g : ℝ → ℂ) = ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  have h := schwartz_norm_mul_integrable (SchwartzMap.derivCLM ℂ ℂ g)
    (SchwartzMap.derivCLM ℂ ℂ g)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [hd]; ring

theorem integrable_weight_sq (g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => x ^ 2 * ‖g x‖ ^ 2) volume := by
  have h := schwartz_norm_mul_integrable (quadraticMulSchwartz g) g
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [quadraticMulSchwartz_apply]
  have hn : ‖((x : ℂ) ^ 2 : ℂ) * g x‖ = x ^ 2 * ‖g x‖ := by
    rw [norm_mul]
    congr 1
    rw [norm_pow]
    simp [sq_abs]
  rw [hn]; ring

/-! ### The main approximation estimate -/

/-- **The weighted-Rellich estimate for one Schwartz function.** -/
theorem approx_estimate (g : SchwartzMap ℝ ℂ) {Rr hh : ℝ} (hRr : 0 < Rr) (hh0 : 0 < hh)
    {n : ℕ} (hn : -Rr + n * hh = Rr) :
    ‖schwartzToL2 g - stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n‖ ^ 2
      ≤ hh ^ 2 * (∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2)
        + (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
  classical
  set c : ℕ → ℂ := fun j => g (-Rr + (j + 1) * hh) with hc
  set v : L2R := stepLp c Rr hh n with hv
  set u : L2R := schwartzToL2 g with hu
  set F : ℝ → ℝ := fun x => ‖g x - stepVal c Rr hh n x‖ ^ 2 with hF
  have hdint := integrable_deriv_sq g
  have hqint := integrable_weight_sq g
  -- identification of `u - v` with `g - s`
  have hae : ⇑(u - v) =ᵐ[volume] fun x => g x - stepVal c Rr hh n x := by
    filter_upwards [Lp.coeFn_sub u v, SchwartzMap.coeFn_toLp g 2 (volume : Measure ℝ),
      stepLp_coeFn c Rr hh n] with x h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply]
    rw [hu, schwartzToL2_apply, h2, hv, h3]
  have hnormsq : ‖u - v‖ ^ 2 = ∫ x : ℝ, F x := by
    rw [norm_sq_eq_integral]
    exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  have hFint : Integrable F volume := by
    have h2 := (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (u - v))).mp (Lp.memLp (u - v))
    exact h2.congr (by filter_upwards [hae] with x hx; rw [hx])
  -- split the integral over `(-R, R]` and its complement
  set U : Set ℝ := Set.Ioc (-Rr) Rr with hU
  have hUeq : (⋃ j ∈ Finset.range n, cellSet Rr hh j) = U := by
    rw [cells_union Rr hh hh0.le n, hn]
  have hsplit : (∫ x in U, F x) + (∫ x in Uᶜ, F x) = ∫ x : ℝ, F x :=
    integral_add_compl measurableSet_Ioc hFint
  -- inside: sum over the cells
  have hUsum : ∫ x in U, F x = ∑ j ∈ Finset.range n, ∫ x in cellSet Rr hh j, F x := by
    rw [← hUeq]
    exact integral_biUnion_finset _ (fun _ _ => measurableSet_Ioc)
      ((cells_disjoint Rr hh hh0).set_pairwise _) (fun _ _ => hFint.integrableOn)
  have hcellbd : ∀ j ∈ Finset.range n, ∫ x in cellSet Rr hh j, F x
      ≤ hh ^ 2 * ∫ x in cellSet Rr hh j, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have heq : ∫ x in cellSet Rr hh j, F x
        = ∫ x in Set.Ioc (-Rr + j * hh) (-Rr + ((j : ℝ) + 1) * hh),
            ‖g x - g (-Rr + ((j : ℝ) + 1) * hh)‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      have : stepVal c Rr hh n x = c j := stepVal_of_mem c hh0 hjn hx
      rw [hF]
      simp only
      rw [this, hc]
    rw [heq]
    have hcell := cell_estimate g (a := -Rr + (j : ℝ) * hh) (b := -Rr + ((j : ℝ) + 1) * hh)
      (by nlinarith)
    have hba : (-Rr + ((j : ℝ) + 1) * hh) - (-Rr + (j : ℝ) * hh) = hh := by ring
    rw [hba] at hcell
    exact hcell
  have hsum2 : ∑ j ∈ Finset.range n, hh ^ 2 * ∫ x in cellSet Rr hh j,
      ‖deriv (g : ℝ → ℂ) x‖ ^ 2
      = hh ^ 2 * ∫ x in U, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
    rw [← Finset.mul_sum, ← integral_biUnion_finset (s := cellSet Rr hh) _
      (fun _ _ => measurableSet_Ioc)
      ((cells_disjoint Rr hh hh0).set_pairwise _) (fun _ _ => hdint.integrableOn), hUeq]
  have hinside : ∫ x in U, F x ≤ hh ^ 2 * ∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
    have h1 : ∫ x in U, F x
        ≤ ∑ j ∈ Finset.range n, hh ^ 2 * ∫ x in cellSet Rr hh j,
            ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
      rw [hUsum]; exact Finset.sum_le_sum hcellbd
    rw [hsum2] at h1
    have h2 : ∫ x in U, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 ≤ ∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 :=
      setIntegral_le_integral hdint (Filter.Eventually.of_forall fun _ => by positivity)
    nlinarith [sq_nonneg hh, h1, h2]
  -- outside: the confining weight
  have htail : ∫ x in Uᶜ, F x ≤ (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
    have hFeq : ∀ x ∈ Uᶜ, F x ≤ x ^ 2 * ‖g x‖ ^ 2 / Rr ^ 2 := by
      intro x hx
      have hstep : stepVal c Rr hh n x = 0 := by
        refine stepVal_of_notMem c hh0.le ?_
        rw [hn]; exact hx
      have hFx : F x = ‖g x‖ ^ 2 := by rw [hF]; simp only; rw [hstep, sub_zero]
      have hx2 : Rr ^ 2 ≤ x ^ 2 := by
        rw [hU, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with h | h
        · nlinarith
        · nlinarith
      rw [hFx, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖g x‖, norm_nonneg (g x)]
    have hmono : ∫ x in Uᶜ, F x ≤ ∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2 / Rr ^ 2 :=
      setIntegral_mono_on hFint.integrableOn
        ((hqint.div_const (Rr ^ 2)).integrableOn) measurableSet_Ioc.compl hFeq
    have hdiv : ∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2 / Rr ^ 2
        = (∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
      rw [integral_div]
    have hle : ∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2 ≤ ∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2 :=
      setIntegral_le_integral hqint (Filter.Eventually.of_forall fun _ => by positivity)
    rw [hdiv] at hmono
    have hpos : (0:ℝ) < Rr ^ 2 := by positivity
    calc ∫ x in Uᶜ, F x ≤ (∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := hmono
      _ ≤ (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
          exact div_le_div_of_nonneg_right hle hpos.le
  rw [hnormsq, ← hsplit]
  linarith [hinside, htail]

end Brockian.Weyl.Rellich

/-! ### The energy form and the good set -/

namespace Brockian.Weyl.OscillatorCompact

open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.HarmonicOscillator
open Brockian.Weyl.Rellich

/-- The oscillator energy of a Schwartz function. -/
noncomputable def energy (g : SchwartzMap ℝ ℂ) : ℝ :=
  (∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2) + ∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2

theorem conj_mul_self (a : ℂ) : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.conj_mul]; norm_cast

theorem energy_nonneg (g : SchwartzMap ℝ ℂ) : 0 ≤ energy g :=
  add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)

/-- The `L²`-image of the Schwartz functions of norm and energy at most `C`. -/
def goodSet (C : ℝ) : Set L2R :=
  {u | ∃ g : SchwartzMap ℝ ℂ, u = schwartzToL2 g ∧ ‖schwartzToL2 g‖ ≤ C ∧ energy g ≤ C}

/-- **The weighted Rellich estimate.** Schwartz states of bounded energy are
uniformly close, in `L²`, to a fixed finite-dimensional space of step
functions. -/
theorem exists_finiteDimensional_approx (C : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Submodule ℂ L2R, FiniteDimensional ℂ V ∧
      ∀ u ∈ goodSet C, ∃ v ∈ V, ‖u - v‖ ≤ ε := by
  classical
  rcases lt_or_ge C 0 with hC | hC
  · refine ⟨⊥, inferInstance, ?_⟩
    rintro u ⟨g, -, -, hen⟩
    exact absurd (le_trans (energy_nonneg g) hen) (not_le.mpr hC)
  -- the geometric parameters
  set Rr : ℝ := 1 + 2 * C / ε ^ 2 with hRrdef
  have hRr1 : (1:ℝ) ≤ Rr := by
    have : 0 ≤ 2 * C / ε ^ 2 := by positivity
    linarith
  have hRr0 : 0 < Rr := by linarith
  have hRrbd : 2 * C ≤ ε ^ 2 * Rr ^ 2 := by
    have h1 : ε ^ 2 * (2 * C / ε ^ 2) = 2 * C := by field_simp
    have h2 : Rr ≤ Rr ^ 2 := by nlinarith
    nlinarith [sq_nonneg ε, hε]
  set δ : ℝ := ε / (2 * (C + 1)) with hδdef
  have hδ0 : 0 < δ := by
    apply div_pos hε
    linarith
  set n : ℕ := ⌈2 * Rr / δ⌉₊ + 1 with hndef
  have hn0 : 0 < n := Nat.succ_pos _
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  set hh : ℝ := 2 * Rr / n with hhdef
  have hh0 : 0 < hh := by
    apply div_pos (by linarith) hnR
  have hhδ : hh ≤ δ := by
    have hceil : 2 * Rr / δ ≤ (n : ℝ) := by
      have := Nat.le_ceil (2 * Rr / δ)
      push_cast [hndef]
      linarith
    rw [hhdef, div_le_iff₀ hnR]
    rw [div_le_iff₀ hδ0] at hceil
    linarith
  have hnhh : -Rr + n * hh = Rr := by
    have hnh : (n : ℝ) * hh = 2 * Rr := by
      rw [hhdef]; field_simp
    linarith
  -- the finite-dimensional space of step functions
  refine ⟨Submodule.span ℂ ↑((Finset.range n).image (cellLp Rr hh)),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_⟩
  rintro u ⟨g, rfl, -, hen⟩
  refine ⟨stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (by simpa using ⟨j, Finset.mem_range.mp hj, rfl⟩)
  · -- the estimate
    have hd0 : 0 ≤ ∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    have hq0 : 0 ≤ ∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2 := integral_nonneg fun _ => by positivity
    have hdC : (∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2) ≤ C := by
      rw [energy] at hen; linarith
    have hqC : (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) ≤ C := by
      rw [energy] at hen; linarith
    have hmain := approx_estimate g hRr0 hh0 hnhh
    -- tail bound
    have htail : (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 ≤ ε ^ 2 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hqC, hRrbd, sq_nonneg Rr]
    -- cell bound
    have hcellb : hh ^ 2 * (∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2) ≤ ε ^ 2 / 2 := by
      have hδ2 : δ ^ 2 * C ≤ ε ^ 2 / 2 := by
        rw [hδdef, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        have hk : C * 2 ≤ (2 * (C + 1)) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hk (sq_nonneg ε)]
      have hh2 : hh ^ 2 ≤ δ ^ 2 := by nlinarith [hh0.le, hδ0.le]
      nlinarith [hd0, hdC, sq_nonneg hh, hh0.le]
    have hfin : ‖schwartzToL2 g - stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n‖ ^ 2
        ≤ ε ^ 2 := by linarith
    nlinarith [norm_nonneg (schwartzToL2 g -
      stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n), hε, hfin]

end Brockian.Weyl.OscillatorCompact

