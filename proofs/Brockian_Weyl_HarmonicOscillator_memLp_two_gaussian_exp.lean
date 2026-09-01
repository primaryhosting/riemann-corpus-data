/-
  RequestProject/ESA.lean

  Essential self-adjointness of the harmonic-oscillator core
  `harmonicOscillatorPMap` (the operator `-d²/dx² + x²` on the Schwartz core of
  `L²(ℝ)`).

  The argument is the classical deficiency-index one.  If `g` is in the domain of
  the adjoint with `T* g = z • g` and `Im z ≠ 0`, then pairing against the Hermite
  functions `hermiteFun n` (which lie in the Schwartz core and satisfy
  `H hermiteFun n = (2n+1) hermiteFun n`) forces `⟪g, hermiteFun n⟫ = 0` for every
  `n`, since `conj z ≠ 2n+1`.  The Hermite functions span every monomial
  `xⁿ e^{-x²/2}`, so all the moments of `x ↦ conj (g x) e^{-x²/2}` vanish, and the
  moment theorem gives `g = 0`.
-/
import RequestProject.Corpus
import RequestProject.Hermite
import RequestProject.Moments

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.Moments

/-! ### Integrability facts for an `L²` function against Gaussian weights -/

theorem memLp_two_gaussian_exp (c : ℝ) :
    MemLp (fun x : ℝ => Real.exp (-(x ^ 2 / 2) + c * |x|)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (-(x ^ 2 / 2) + c * |x|))
      (volume : Measure ℝ) := by fun_prop
  rw [memLp_two_iff_integrable_sq hmeas]
  have hb : Integrable (fun x : ℝ => Real.exp (2 * c ^ 2) * Real.exp (-(1 / 2) * x ^ 2))
      (volume : Measure ℝ) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  refine Integrable.mono' hb (by fun_prop) ?_
  filter_upwards with x
  have hx : -(x ^ 2) + 2 * c * |x| ≤ 2 * c ^ 2 + -(1 / 2) * x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 2 * c), sq_abs x, abs_nonneg x]
  have h1 : (Real.exp (-(x ^ 2 / 2) + c * |x|)) ^ 2
      = Real.exp (-(x ^ 2) + 2 * c * |x|) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), h1, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hx

theorem integrable_norm_mul_exp (g : Lp ℂ 2 (volume : Measure ℝ)) (c : ℝ) :
    Integrable (fun x : ℝ =>
      ‖(starRingEnd ℂ) (g x) * (Real.exp (-(x ^ 2 / 2)) : ℂ)‖ * Real.exp (c * |x|))
      (volume : Measure ℝ) := by
  have hfun : (fun x : ℝ =>
        ‖(starRingEnd ℂ) (g x) * (Real.exp (-(x ^ 2 / 2)) : ℂ)‖ * Real.exp (c * |x|))
      = (fun x : ℝ => ‖g x‖) * (fun x : ℝ => Real.exp (-(x ^ 2 / 2) + c * |x|)) := by
    funext x
    have h1 : ‖(starRingEnd ℂ) (g x) * (Real.exp (-(x ^ 2 / 2)) : ℂ)‖
        = ‖g x‖ * Real.exp (-(x ^ 2 / 2)) := by
      rw [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_pos _).le]
    rw [h1, Pi.mul_apply, Real.exp_add]
    ring
  rw [hfun]
  exact MemLp.integrable_mul (Lp.memLp g).norm (memLp_two_gaussian_exp c)

/-! ### The deficiency spaces are trivial -/

/-- The inner product of an `L²` function against an embedded Schwartz function
is the corresponding integral. -/
theorem inner_schwartzToL2 (g : L2R) (f : SchwartzMap ℝ ℂ) :
    ⟪g, schwartzToL2 f⟫_ℂ = ∫ x : ℝ, (starRingEnd ℂ) (g x) * f x := by
  rw [schwartzToL2_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [f.coeFn_toLp 2 (volume : Measure ℝ)] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

/-- **Both deficiency spaces of the harmonic-oscillator core are trivial.**
For any non-real `z`, `ker (T* - z) = ⊥`. -/
theorem harmonicOscillator_deficiency_eq_bot {z : ℂ} (hz : z.im ≠ 0) :
    deficiencySpace harmonicOscillatorPMap z = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [mem_deficiencySpace_iff] at hg
  have hFA := LinearPMap.adjoint_isFormalAdjoint harmonicOscillatorPMap_dense
  -- the adjoint relation, read on the Schwartz core
  have key : ∀ f : SchwartzMap ℝ ℂ,
      (starRingEnd ℂ) z * ⟪(g : L2R), schwartzToL2 f⟫_ℂ
        = ⟪(g : L2R), schwartzToL2 (oscillatorSchwartz f)⟫_ℂ := by
    intro f
    have hmem : schwartzToL2 f ∈ harmonicOscillatorPMap.domain := ⟨f, rfl⟩
    have hx : (⟨schwartzToL2 f, hmem⟩ : harmonicOscillatorPMap.domain)
        = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
      Subtype.ext (by rw [LinearEquiv.ofInjective_apply])
    have h := hFA g ⟨schwartzToL2 f, hmem⟩
    rw [hg, inner_smul_left, hx, harmonicOscillatorPMap_toFun_ofInjective,
      oscillatorCoreMap_apply] at h
    exact h
  -- the linear functional `f ↦ ⟪g, f⟫` on the Schwartz core
  set Lam : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ :=
    (innerSL ℂ (g : L2R)).toLinearMap.comp schwartzToL2 with hLam
  have hLam_apply : ∀ f : SchwartzMap ℝ ℂ, Lam f = ⟪(g : L2R), schwartzToL2 f⟫_ℂ := fun f => rfl
  -- it kills the Hermite functions
  have hherm : ∀ n : ℕ, Lam (hermiteFun n) = 0 := by
    intro n
    have h := key (hermiteFun n)
    rw [oscillator_hermiteFun n, map_smul, inner_smul_right] at h
    have hne : (starRingEnd ℂ) z ≠ (2 * n + 1 : ℂ) := by
      intro heq
      have h1 : ((starRingEnd ℂ) z).im = -z.im := Complex.conj_im z
      rw [heq] at h1
      have h2 : ((2 * (n : ℂ) + 1)).im = 0 := by simp
      rw [h2] at h1
      exact hz (by linarith)
    have hfac : ((starRingEnd ℂ) z - (2 * n + 1 : ℂ)) * ⟪(g : L2R), schwartzToL2 (hermiteFun n)⟫_ℂ
        = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne
    · rw [hLam_apply]; exact h1
  -- hence it kills the whole span, in particular every monomial `xⁿ e^{-x²/2}`
  have hspan : Submodule.span ℂ (Set.range hermiteFun) ≤ LinearMap.ker Lam := by
    rw [Submodule.span_le]
    rintro u ⟨n, rfl⟩
    exact hherm n
  have hpsi : ∀ n : ℕ, Lam (psiFun n) = 0 := fun n => hspan (psiFun_mem_hermiteSpan n)
  -- all moments of `G x = conj (g x) e^{-x²/2}` vanish
  set G : ℝ → ℂ := fun x => (starRingEnd ℂ) (((g : L2R) : ℝ → ℂ) x)
    * (Real.exp (-(x ^ 2 / 2)) : ℂ) with hG
  have hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * G x = 0 := by
    intro n
    have h := hpsi n
    rw [hLam_apply, inner_schwartzToL2] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hG, psiFun_apply]
    ring
  have hmeasG : AEStronglyMeasurable G (volume : Measure ℝ) := by
    have h1 : AEStronglyMeasurable (fun x : ℝ => ((g : L2R) : ℝ → ℂ) x) (volume : Measure ℝ) :=
      Lp.aestronglyMeasurable (g : L2R)
    exact (Complex.continuous_conj.comp_aestronglyMeasurable h1).mul (by fun_prop)
  have hintG : ∀ c : ℝ, Integrable (fun x : ℝ => ‖G x‖ * Real.exp (c * |x|))
      (volume : Measure ℝ) := fun c => integrable_norm_mul_exp (g : L2R) c
  have hzero : G =ᵐ[volume] 0 := ae_eq_zero_of_moments_eq_zero hmeasG hintG hmom
  -- therefore `g = 0`
  have hgzero : (g : L2R) = 0 := by
    have hae : ((g : L2R) : ℝ → ℂ) =ᵐ[volume] 0 := by
      filter_upwards [hzero] with x hx
      have hexp : (Real.exp (-(x ^ 2 / 2)) : ℂ) ≠ 0 := by simp
      rcases mul_eq_zero.mp hx with h1 | h1
      · have h2 := congrArg (starRingEnd ℂ) h1
        simpa using h2
      · exact absurd h1 hexp
    exact (Lp.eq_zero_iff_ae_eq_zero).mpr hae
  exact Submodule.coe_eq_zero.mp hgzero

/-- **Essential self-adjointness of the harmonic-oscillator core.** -/
theorem harmonicOscillatorPMap_essentiallySelfAdjoint :
    EssentiallySelfAdjoint harmonicOscillatorPMap :=
  ⟨harmonicOscillator_deficiency_eq_bot (by rw [Complex.I_im]; exact one_ne_zero),
   harmonicOscillator_deficiency_eq_bot (by simp [Complex.neg_im, Complex.I_im])⟩

end Brockian.Weyl.HarmonicOscillator

/-
  RequestProject/Hermite.lean

  Hermite functions for the Schwartz-core harmonic oscillator
  `oscillatorSchwartz f = -f'' + x² f`.

  We use the creation operator `A† f = x f - f'`, which maps the Schwartz space
  to itself.  Starting from the Gaussian `h₀ = e^{-x²/2}` (an eigenfunction with
  eigenvalue `1`), the functions `hermiteFun n = (A†)ⁿ h₀` are eigenfunctions with
  eigenvalue `2n+1`, and their span contains every `x ↦ xⁿ e^{-x²/2}`.
-/
import RequestProject.Corpus
import RequestProject.GaussianSchwartz

open SchwartzMap Brockian.Gaussian

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.SchrodingerMinimal

/-! ### Multiplication by `x` and the creation operator -/

theorem x_hasTemperateGrowth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop

/-- Multiplication by `x` on the Schwartz space. -/
noncomputable def xMulSchwartz : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

@[simp] theorem xMulSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    xMulSchwartz f x = (x : ℂ) * f x := by
  rw [xMulSchwartz]
  simpa [smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply x_hasTemperateGrowth f x

/-- The creation operator `A† f = x f - f'`. -/
noncomputable def creationSchwartz : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  xMulSchwartz - SchwartzMap.derivCLM ℂ ℂ

@[simp] theorem creationSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    creationSchwartz f x = (x : ℂ) * f x - deriv f x := by
  simp [creationSchwartz]

/-! ### Basic derivative computations -/

theorem hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x))

/-- The coercion of `A† f`. -/
theorem coe_creation (f : SchwartzMap ℝ ℂ) :
    (creationSchwartz f : ℝ → ℂ) = fun y : ℝ => (y : ℂ) * f y - deriv (f : ℝ → ℂ) y := by
  funext y; simp

/-- The coercion of the oscillator applied to `f`. -/
theorem coe_oscillator (f : SchwartzMap ℝ ℂ) :
    (oscillatorSchwartz f : ℝ → ℂ)
      = fun y : ℝ => -deriv (deriv (f : ℝ → ℂ)) y + (y : ℂ) ^ 2 * f y := by
  funext y; simp

/-- Derivative of the coercion of a Schwartz map, as a `HasDerivAt` statement. -/
theorem schwartz_hasDerivAt (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (f : ℝ → ℂ) (deriv (f : ℝ → ℂ) x) x :=
  f.differentiableAt.hasDerivAt

/-- `deriv f` is again the coercion of a Schwartz map. -/
theorem coe_derivCLM (f : SchwartzMap ℝ ℂ) :
    ((SchwartzMap.derivCLM ℂ ℂ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (f : ℝ → ℂ) := rfl

/-- Derivative of `x ↦ x g x` for a Schwartz `g`. -/
theorem hasDerivAt_xmul (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * g y) (g x + (x : ℂ) * deriv (g : ℝ → ℂ) x) x := by
  simpa using (hasDerivAt_ofReal x).mul (schwartz_hasDerivAt g x)

/-- Derivative of `A† f`. -/
theorem deriv_creation (f : SchwartzMap ℝ ℂ) :
    deriv ((creationSchwartz f : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => f y + (y : ℂ) * deriv (f : ℝ → ℂ) y - deriv (deriv (f : ℝ → ℂ)) y := by
  funext x
  rw [coe_creation]
  have h2 : HasDerivAt (deriv (f : ℝ → ℂ)) (deriv (deriv (f : ℝ → ℂ)) x) x := by
    have h := schwartz_hasDerivAt (SchwartzMap.derivCLM ℂ ℂ f) x
    rwa [coe_derivCLM] at h
  exact ((hasDerivAt_xmul f x).sub h2).deriv

/-- **The commutation identity** `H (A† f) = A† (H f) + 2 A† f`, where
`H = -d²/dx² + x²`. -/
theorem oscillator_creation (f : SchwartzMap ℝ ℂ) :
    oscillatorSchwartz (creationSchwartz f)
      = creationSchwartz (oscillatorSchwartz f) + (2 : ℂ) • creationSchwartz f := by
  ext x
  set f1 : ℝ → ℂ := deriv (f : ℝ → ℂ) with hf1
  set f2 : ℝ → ℂ := deriv f1 with hf2
  set f3 : ℝ → ℂ := deriv f2 with hf3
  have hd1 : HasDerivAt (f : ℝ → ℂ) (f1 x) x := schwartz_hasDerivAt f x
  have hd2 : HasDerivAt f1 (f2 x) x := by
    have h := schwartz_hasDerivAt (SchwartzMap.derivCLM ℂ ℂ f) x
    simp only [coe_derivCLM] at h
    exact h
  have hd3 : HasDerivAt f2 (f3 x) x := by
    have h := schwartz_hasDerivAt (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) x
    simp only [coe_derivCLM] at h
    exact h
  have hB : deriv (deriv ((creationSchwartz f : SchwartzMap ℝ ℂ) : ℝ → ℂ)) x
      = f1 x + (f1 x + (x : ℂ) * f2 x) - f3 x := by
    rw [deriv_creation]
    exact ((hd1.add (by simpa using (hasDerivAt_ofReal x).mul hd2)).sub hd3).deriv
  have hC : deriv ((oscillatorSchwartz f : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = -f3 x + (2 * (x : ℂ) * f x + (x : ℂ) ^ 2 * f1 x) := by
    rw [coe_oscillator]
    exact (hd3.neg.add (by simpa using ((hasDerivAt_ofReal x).pow 2).mul hd1)).deriv
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, oscillatorSchwartz_apply,
    creationSchwartz_apply, hB, hC, smul_eq_mul, ← hf1, ← hf2]
  ring

/-! ### The Gaussian is an eigenfunction -/

theorem hasDerivAt_cgauss (x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.exp (-(y ^ 2 / 2)) : ℂ))
      (-(x : ℂ) * (Real.exp (-(x ^ 2 / 2)) : ℂ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    simpa using ((hasDerivAt_pow 2 x).div_const 2).neg
  have hr : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      ((-x) * Real.exp (-(x ^ 2 / 2))) x := by
    simpa [mul_comm] using h1.exp
  simpa using hr.ofReal_comp

theorem deriv_cgauss :
    deriv ((gaussianSchwartz : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => -(y : ℂ) * (Real.exp (-(y ^ 2 / 2)) : ℂ) := by
  funext x
  exact (hasDerivAt_cgauss x).deriv

/-- The Gaussian is an eigenfunction of `H = -d²/dx² + x²` with eigenvalue `1`. -/
theorem oscillator_gaussian :
    oscillatorSchwartz gaussianSchwartz = gaussianSchwartz := by
  ext x
  have h2 : deriv (deriv ((gaussianSchwartz : SchwartzMap ℝ ℂ) : ℝ → ℂ)) x
      = ((x : ℂ) ^ 2 - 1) * (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
    rw [deriv_cgauss]
    have hd : HasDerivAt (fun y : ℝ => -(y : ℂ) * (Real.exp (-(y ^ 2 / 2)) : ℂ))
        (-1 * (Real.exp (-(x ^ 2 / 2)) : ℂ)
          + (-(x : ℂ)) * (-(x : ℂ) * (Real.exp (-(x ^ 2 / 2)) : ℂ))) x :=
      (hasDerivAt_ofReal x).neg.mul (hasDerivAt_cgauss x)
    rw [hd.deriv]
    ring
  simp only [oscillatorSchwartz_apply, h2, gaussianSchwartz_apply]
  ring

/-! ### The Hermite functions and the monomial family -/

/-- The Hermite functions `hermiteFun n = (A†)ⁿ e^{-x²/2}`. -/
noncomputable def hermiteFun (n : ℕ) : SchwartzMap ℝ ℂ :=
  (creationSchwartz : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[n] gaussianSchwartz

theorem hermiteFun_zero : hermiteFun 0 = gaussianSchwartz := rfl

theorem hermiteFun_succ (n : ℕ) :
    hermiteFun (n + 1) = creationSchwartz (hermiteFun n) := by
  rw [hermiteFun, hermiteFun, Function.iterate_succ_apply']

/-- **The Hermite functions are eigenfunctions**: `H hermiteFun n = (2n+1) hermiteFun n`. -/
theorem oscillator_hermiteFun (n : ℕ) :
    oscillatorSchwartz (hermiteFun n) = ((2 * n + 1 : ℂ)) • hermiteFun n := by
  induction n with
  | zero => simpa [hermiteFun_zero] using oscillator_gaussian
  | succ k ih =>
      rw [hermiteFun_succ, oscillator_creation, ih, map_smul]
      push_cast
      module

/-- The monomial family `psiFun n = xⁿ e^{-x²/2}`. -/
noncomputable def psiFun (n : ℕ) : SchwartzMap ℝ ℂ :=
  (xMulSchwartz : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ)^[n] gaussianSchwartz

theorem psiFun_zero : psiFun 0 = gaussianSchwartz := rfl

theorem psiFun_succ (n : ℕ) : psiFun (n + 1) = xMulSchwartz (psiFun n) := by
  rw [psiFun, psiFun, Function.iterate_succ_apply']

@[simp] theorem psiFun_apply (n : ℕ) (x : ℝ) :
    psiFun n x = (x : ℂ) ^ n * (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
  induction n with
  | zero => simp [psiFun_zero]
  | succ k ih => rw [psiFun_succ, xMulSchwartz_apply, ih]; ring

theorem deriv_psiFun (n : ℕ) (x : ℝ) :
    deriv ((psiFun n : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = (n : ℂ) * (x : ℂ) ^ (n - 1) * (Real.exp (-(x ^ 2 / 2)) : ℂ)
        - (x : ℂ) ^ (n + 1) * (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
  have hfun : ((psiFun n : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => (y : ℂ) ^ n * (Real.exp (-(y ^ 2 / 2)) : ℂ) := funext (psiFun_apply n)
  rw [hfun]
  have hd : HasDerivAt (fun y : ℝ => (y : ℂ) ^ n * (Real.exp (-(y ^ 2 / 2)) : ℂ))
      (((n : ℂ) * (x : ℂ) ^ (n - 1) * 1) * (Real.exp (-(x ^ 2 / 2)) : ℂ)
        + (x : ℂ) ^ n * (-(x : ℂ) * (Real.exp (-(x ^ 2 / 2)) : ℂ))) x :=
    ((hasDerivAt_ofReal x).pow n).mul (hasDerivAt_cgauss x)
  rw [hd.deriv]
  ring

/-- The creation operator on the monomial family:
`A† (xⁿ e^{-x²/2}) = 2 xⁿ⁺¹ e^{-x²/2} - n xⁿ⁻¹ e^{-x²/2}`. -/
theorem creation_psiFun (n : ℕ) :
    creationSchwartz (psiFun n) = (2 : ℂ) • psiFun (n + 1) - (n : ℂ) • psiFun (n - 1) := by
  ext x
  simp only [creationSchwartz_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul,
    psiFun_apply, deriv_psiFun]
  cases n with
  | zero => simp; ring
  | succ m => simp only [Nat.add_sub_cancel]; push_cast; ring

/-! ### The Hermite functions span the monomial family -/

theorem hermiteSpan_creation_mem {u : SchwartzMap ℝ ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range hermiteFun)) :
    creationSchwartz u ∈ Submodule.span ℂ (Set.range hermiteFun) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨k, rfl⟩ := hu
      exact Submodule.subset_span ⟨k + 1, (hermiteFun_succ k).symm ▸ rfl⟩
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- Every monomial `xⁿ e^{-x²/2}` lies in the span of the Hermite functions. -/
theorem psiFun_mem_hermiteSpan (n : ℕ) :
    psiFun n ∈ Submodule.span ℂ (Set.range hermiteFun) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact Submodule.subset_span ⟨0, rfl⟩
    | (m + 1) =>
        have h1 := ih m (by omega)
        have h2 := ih (m - 1) (by omega)
        have hrec := creation_psiFun m
        have hval : psiFun (m + 1)
            = (2 : ℂ)⁻¹ • (creationSchwartz (psiFun m) + (m : ℂ) • psiFun (m - 1)) := by
          rw [hrec]
          match_scalars <;> ring
        rw [hval]
        exact Submodule.smul_mem _ _
          (Submodule.add_mem _ (hermiteSpan_creation_mem h1) (Submodule.smul_mem _ _ h2))

end Brockian.Weyl.HarmonicOscillator

/-
  RequestProject/Corpus.lean

  The corpus declarations needed for the harmonic-oscillator goal, reproduced
  here (verbatim where they were supplied, and reconstructed minimally where the
  supplying module was not part of the prompt).

  * `Brockian.Weyl.Operator`            — verbatim from `Brockian/WeylOperator.lean`.
  * `Brockian.Weyl.SchrodingerMinimal`  — the pieces of `Brockian/WeylSchrodingerMinimal.lean`
                                          that the harmonic-oscillator module uses
                                          (`H2`, `schwartzToL2`, `D2`, `inner_toLp`, ...).
  * `Brockian.Weyl.HarmonicOscillator`  — verbatim from `Brockian/WeylHarmonicOscillator.lean`
                                          (the operator itself and its density statement).
-/
import Mathlib

namespace Brockian.Weyl.Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Symmetric densely-defined operators -/

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

/-! ### The basic symmetric-operator inequality -/

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

/-! ### Deficiency spaces and essential self-adjointness -/

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

/-! ### Gate-0 witness: a concrete symmetric operator -/

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

/-! ## The `L²`-core scaffolding (`Brockian/WeylSchrodingerMinimal.lean`)

Only the declarations used by the harmonic-oscillator module are reproduced. -/

namespace Brockian.Weyl.SchrodingerMinimal

open MeasureTheory SchwartzMap ComplexConjugate
open scoped InnerProductSpace

/-- The Hilbert space `L²(ℝ, ℂ)`. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The Schwartz core, embedded into `L²(ℝ)`. -/
noncomputable def schwartzToL2 : SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

@[simp] theorem schwartzToL2_apply (f : SchwartzMap ℝ ℂ) :
    schwartzToL2 f = f.toLp 2 (volume : Measure ℝ) := rfl

theorem schwartzToL2_injective : Function.Injective schwartzToL2 := by
  intro f g hfg
  have hf := f.coeFn_toLp 2 (volume : Measure ℝ)
  have hg := g.coeFn_toLp 2 (volume : Measure ℝ)
  have hae : (f : ℝ → ℂ) =ᵐ[volume] (g : ℝ → ℂ) := by
    have : (f.toLp 2 (volume : Measure ℝ) : ℝ → ℂ) =ᵐ[volume]
        (g.toLp 2 (volume : Measure ℝ) : ℝ → ℂ) := by
      rw [show f.toLp 2 (volume : Measure ℝ) = g.toLp 2 (volume : Measure ℝ) from hfg]
    filter_upwards [hf, hg, this] with x hx hy hz
    rw [← hx, ← hy, hz]
  exact SchwartzMap.ext
    (congrFun ((f.continuous.ae_eq_iff_eq (volume : Measure ℝ) g.continuous).mp hae))

/-- The second derivative on the Schwartz core. -/
noncomputable def D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ)

@[simp] theorem D2_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    D2 f x = deriv (deriv f) x := rfl

/-- The `L²` inner product of two embedded Schwartz functions is the integral. -/
theorem inner_toLp (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 f) (schwartzToL2 g) = ∫ x : ℝ, conj (f x) * g x := by
  rw [schwartzToL2_apply, schwartzToL2_apply,
    SchwartzMap.inner_toL2_toL2_eq f g (volume : Measure ℝ)]
  simp only [RCLike.inner_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

end Brockian.Weyl.SchrodingerMinimal

/-! ## The harmonic oscillator on the Schwartz core
(`Brockian/WeylHarmonicOscillator.lean`, verbatim up to the confining-shape part). -/

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
  have h : oscillatorSchwartz f = -(D2 f) + quadraticMulSchwartz f := rfl
  rw [oscillatorCoreMap_apply, h, map_add, map_neg]

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

/-- The harmonic oscillator has the same dense Schwartz domain as the free core. -/
theorem harmonicOscillatorPMap_dense :
    Dense (harmonicOscillatorPMap.domain : Set L2R) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → L2R)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f
    rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [harmonicOscillatorPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

end Brockian.Weyl.HarmonicOscillator

/-
  RequestProject/GaussianSchwartz.lean

  The Gaussian `x ↦ exp (-x²/2)` as an element of the complex Schwartz space
  `𝓢(ℝ, ℂ)`.  All its derivatives are Hermite polynomials times the Gaussian
  (`Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`), and every polynomial
  times the Gaussian is bounded, which is exactly the Schwartz decay condition.
-/
import Mathlib

open Real Nat Polynomial SchwartzMap

namespace Brockian.Gaussian

/-- `|x|^m e^{-x²/2}` is bounded by `m! 2^m + 1`. -/
theorem pow_abs_mul_gauss_le (m : ℕ) (x : ℝ) :
    |x| ^ m * Real.exp (-(x ^ 2 / 2)) ≤ (m ! : ℝ) * 2 ^ m + 1 := by
  have hfac : (0 : ℝ) < (m ! : ℝ) := by positivity
  have hf1 : (1 : ℝ) ≤ (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rcases le_or_gt |x| 1 with h | h
  · have h1 : |x| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    have h2 : Real.exp (-(x ^ 2 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have h3 : (0 : ℝ) ≤ |x| ^ m := by positivity
    have h4 : (0 : ℝ) < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
    have h5 : (1 : ℝ) ≤ (m ! : ℝ) * 2 ^ m := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      nlinarith
    nlinarith
  · have hx0 : (0 : ℝ) < |x| := lt_trans zero_lt_one h
    have key : (x ^ 2 / 2) ^ m / (m ! : ℝ) ≤ Real.exp (x ^ 2 / 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) m
    have hxm : (x ^ 2 / 2) ^ m = |x| ^ (2 * m) / 2 ^ m := by
      rw [div_pow, pow_mul, sq_abs]
    have hexp : Real.exp (-(x ^ 2 / 2)) = (Real.exp (x ^ 2 / 2))⁻¹ := by rw [Real.exp_neg]
    have hpos : (0 : ℝ) < Real.exp (x ^ 2 / 2) := Real.exp_pos _
    have hlow : |x| ^ (2 * m) / (2 ^ m * (m ! : ℝ)) ≤ Real.exp (x ^ 2 / 2) := by
      rw [hxm] at key
      calc |x| ^ (2 * m) / (2 ^ m * (m ! : ℝ))
          = |x| ^ (2 * m) / 2 ^ m / (m ! : ℝ) := by rw [div_div]
        _ ≤ _ := key
    have hxpos : (0 : ℝ) < |x| ^ m := by positivity
    have h2m : |x| ^ (2 * m) = |x| ^ m * |x| ^ m := by rw [two_mul, pow_add]
    have hmain : |x| ^ m * Real.exp (-(x ^ 2 / 2)) ≤ (m ! : ℝ) * 2 ^ m := by
      rw [hexp, mul_inv_le_iff₀ hpos]
      calc |x| ^ m ≤ (m ! : ℝ) * 2 ^ m * (|x| ^ (2 * m) / (2 ^ m * (m ! : ℝ))) := by
            rw [h2m]
            have h2p : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
            field_simp
            nlinarith [one_le_pow₀ (le_of_lt h) (n := m)]
        _ ≤ (m ! : ℝ) * 2 ^ m * Real.exp (x ^ 2 / 2) := by gcongr
    linarith

/-- A polynomial times the Gaussian, times any power of `|x|`, is bounded. -/
theorem poly_gauss_bounded (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * (|p.eval x| * Real.exp (-(x ^ 2 / 2))) ≤ C := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1),
    |p.coeff i| * (((k + i)! : ℝ) * 2 ^ (k + i) + 1), fun x => ?_⟩
  have habs : |p.eval x| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
    rw [p.eval_eq_sum_range]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_pow]
  have hnn : (0 : ℝ) ≤ |x| ^ k * Real.exp (-(x ^ 2 / 2)) := by positivity
  calc |x| ^ k * (|p.eval x| * Real.exp (-(x ^ 2 / 2)))
      = (|x| ^ k * Real.exp (-(x ^ 2 / 2))) * |p.eval x| := by ring
    _ ≤ (|x| ^ k * Real.exp (-(x ^ 2 / 2))) *
          ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
        exact mul_le_mul_of_nonneg_left habs hnn
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
          |p.coeff i| * (|x| ^ (k + i) * Real.exp (-(x ^ 2 / 2))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add]; ring
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
          |p.coeff i| * (((k + i)! : ℝ) * 2 ^ (k + i) + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (pow_abs_mul_gauss_le (k + i) x) (abs_nonneg _)

/-- The real Gaussian. -/
noncomputable def gaussReal : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2))

theorem contDiff_gaussReal : ContDiff ℝ (⊤ : ℕ∞) gaussReal := by
  unfold gaussReal; fun_prop

theorem iteratedDeriv_gaussReal (n : ℕ) (x : ℝ) :
    iteratedDeriv n gaussReal x
      = (-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  rw [iteratedDeriv_eq_iterate]
  exact Polynomial.deriv_gaussian_eq_hermite_mul_gaussian n x

/-- **The Gaussian as a Schwartz function** `x ↦ exp (-x²/2) : 𝓢(ℝ, ℂ)`. -/
noncomputable def gaussianSchwartz : SchwartzMap ℝ ℂ where
  toFun := fun x => (Real.exp (-(x ^ 2 / 2)) : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp
    (show ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) by fun_prop)
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := poly_gauss_bounded ((hermite n).map (Int.castRingHom ℝ)) k
    refine ⟨C, fun x => ?_⟩
    have hnorm : ‖iteratedFDeriv ℝ n (fun y : ℝ => ((gaussReal y : ℝ) : ℂ)) x‖
        = ‖iteratedDeriv n gaussReal x‖ := by
      have := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f := gaussReal) (x := x)
        contDiff_gaussReal.contDiffAt (i := n) (by exact_mod_cast le_top)
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact this
    have hfun : (fun y : ℝ => ((Real.exp (-(y ^ 2 / 2)) : ℝ) : ℂ))
        = fun y : ℝ => ((gaussReal y : ℝ) : ℂ) := rfl
    rw [hfun, hnorm, iteratedDeriv_gaussReal]
    have hev : (aeval x (hermite n) : ℝ)
        = ((hermite n).map (Int.castRingHom ℝ)).eval x := by simp [aeval_def, eval_map]
    rw [hev]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Real.abs_exp]
    exact hC x

@[simp] theorem gaussianSchwartz_apply (x : ℝ) :
    gaussianSchwartz x = (Real.exp (-(x ^ 2 / 2)) : ℂ) := rfl

end Brockian.Gaussian

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
  RequestProject/Moments.lean

  A moment-vanishing theorem: a function on `ℝ` with uniform exponential
  integrability all of whose moments `∫ xⁿ G x` vanish is zero almost everywhere.

  The proof expands `exp (w x)` in its power series inside the integral (all the
  moments kill it), which shows that the Fourier transform of `G` vanishes
  identically; pairing against Schwartz test functions and using that the Fourier
  transform is onto the Schwartz space then gives `∫ φ G = 0` for every smooth
  compactly supported `φ`, whence `G = 0` a.e.
-/
import Mathlib

open MeasureTheory Complex Real Filter
open scoped FourierTransform ENNReal Nat

namespace Brockian.Moments

section

variable {G : ℝ → ℂ}
  (hmeas : AEStronglyMeasurable G volume)
  (hint : ∀ c : ℝ, Integrable (fun x : ℝ => ‖G x‖ * Real.exp (c * |x|)) volume)

include hmeas hint

/-- Under the exponential-integrability hypothesis, all the functions
`x ↦ xⁿ G x` are integrable. -/
theorem integrable_pow_mul (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * G x) volume := by
  refine Integrable.mono' (((hint 1).const_mul (n ! : ℝ))) ?_ ?_
  · exact (Complex.continuous_ofReal.aestronglyMeasurable.pow n).mul hmeas
  · filter_upwards with x
    have hpow : |x| ^ n ≤ (n ! : ℝ) * Real.exp |x| := by
      have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
      have hn : (0 : ℝ) < (n ! : ℝ) := by positivity
      rw [div_le_iff₀ hn] at h
      linarith
    have hG : (0 : ℝ) ≤ ‖G x‖ := norm_nonneg _
    calc ‖(x : ℂ) ^ n * G x‖ = |x| ^ n * ‖G x‖ := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ((n ! : ℝ) * Real.exp |x|) * ‖G x‖ := by gcongr
      _ = (n ! : ℝ) * (‖G x‖ * Real.exp (1 * |x|)) := by rw [one_mul]; ring

variable (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * G x = 0)

include hmom

/-- The exponential integral `∫ exp (w x) G x` vanishes for every complex `w`:
expand the exponential in its power series and use the vanishing moments. -/
theorem integral_cexp_mul_eq_zero (w : ℂ) :
    ∫ x : ℝ, Complex.exp (w * x) * G x = 0 := by
  set F : ℕ → ℝ → ℂ := fun n x => (w ^ n / (n ! : ℂ)) * ((x : ℂ) ^ n * G x) with hFdef
  have hmeasF : ∀ n, AEStronglyMeasurable (F n) volume := fun n =>
    AEStronglyMeasurable.const_mul
      ((Complex.continuous_ofReal.aestronglyMeasurable.pow n).mul hmeas) _
  have hnorm : ∀ (n : ℕ) (x : ℝ), ‖F n x‖ = (‖w‖ * |x|) ^ n / (n ! : ℝ) * ‖G x‖ := by
    intro n x
    simp only [hFdef, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast, mul_pow]
    ring
  -- the pointwise sum of the norms
  have hsumnorm : ∀ x : ℝ, ∑' n : ℕ, ‖F n x‖ = Real.exp (‖w‖ * |x|) * ‖G x‖ := by
    intro x
    simp only [hnorm]
    rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsummable : ∀ x : ℝ, Summable fun n : ℕ => ‖F n x‖ := by
    intro x
    simp only [hnorm]
    exact (Real.summable_pow_div_factorial (‖w‖ * |x|)).mul_right _
  -- finiteness of the sum of the `L¹` norms
  have hfin : ∑' n : ℕ, ∫⁻ x : ℝ, ‖F n x‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun n => (hmeasF n).enorm)]
    have hpt : ∀ x : ℝ, ∑' n : ℕ, ‖F n x‖ₑ
        = ENNReal.ofReal (‖G x‖ * Real.exp (‖w‖ * |x|)) := by
      intro x
      have : ∀ n : ℕ, ‖F n x‖ₑ = ENNReal.ofReal ‖F n x‖ := fun n => by
        rw [← ofReal_norm_eq_enorm]
      simp only [this]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hsummable x), hsumnorm x,
        mul_comm]
    rw [lintegral_congr hpt]
    have hI := (hint ‖w‖).hasFiniteIntegral
    have heq : ∀ x : ℝ, ‖‖G x‖ * Real.exp (‖w‖ * |x|)‖ₑ
        = ENNReal.ofReal (‖G x‖ * Real.exp (‖w‖ * |x|)) := by
      intro x
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖G x‖ * Real.exp (‖w‖ * |x|))]
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm] at hI
    rw [lintegral_congr heq] at hI
    exact hI.ne
  have hpt : ∀ x : ℝ, ∑' n : ℕ, F n x = Complex.exp (w * x) * G x := by
    intro x
    have hexp : Complex.exp (w * x) = ∑' n : ℕ, (w * (x : ℂ)) ^ n / (n ! : ℂ) := by
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    rw [hexp, ← tsum_mul_right]
    exact tsum_congr fun n => by simp only [hFdef, mul_pow]; ring
  calc ∫ x : ℝ, Complex.exp (w * x) * G x
      = ∫ x : ℝ, ∑' n : ℕ, F n x := by simp_rw [hpt]
    _ = ∑' n : ℕ, ∫ x : ℝ, F n x := integral_tsum hmeasF hfin
    _ = 0 := by
        have : ∀ n : ℕ, ∫ x : ℝ, F n x = 0 := by
          intro n
          simp only [hFdef]
          rw [MeasureTheory.integral_const_mul, hmom n, mul_zero]
        simp [this]

/-- The Fourier transform of `G` vanishes identically. -/
theorem fourier_eq_zero (ξ : ℝ) : 𝓕 G ξ = 0 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∀ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) • G v
      = Complex.exp (((-2 * π * ξ : ℝ) * Complex.I) * v) * G v := by
    intro v
    congr 2
    push_cast
    ring
  simp_rw [this]
  exact integral_cexp_mul_eq_zero hmeas hint hmom _

/-- **Moment theorem.** A function with uniform exponential integrability whose
moments `∫ xⁿ G x` all vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_moments_eq_zero : G =ᵐ[volume] 0 := by
  have hGint : Integrable G volume := by
    simpa using integrable_pow_mul hmeas hint 0
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hGint.locallyIntegrable ?_
  intro g hg hgsupp
  -- package `g` as a complex-valued Schwartz function
  have hsupp : HasCompactSupport (fun x : ℝ => (g x : ℂ)) :=
    hgsupp.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hdiff := Complex.ofRealCLM.contDiff.comp hg
  set phi : SchwartzMap ℝ ℂ := hsupp.toSchwartzMap hdiff with hphi
  set psi : SchwartzMap ℝ ℂ := 𝓕⁻ phi with hpsi
  have hfp : 𝓕 psi = phi := FourierTransform.fourier_fourierInv_eq phi
  have hflip : ((innerₗ ℝ).flip : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) = innerₗ ℝ := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    exact real_inner_comm x y
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop) hGint
    (psi.integrable (μ := (volume : Measure ℝ)))
  rw [hflip] at hswap
  replace hswap : ∫ ξ : ℝ, (𝓕 G ξ) • (psi ξ) = ∫ x : ℝ, G x • (𝓕 (⇑psi) x) := hswap
  have hzero : ∫ ξ : ℝ, (𝓕 G ξ) • (psi ξ) = 0 := by
    simp [fourier_eq_zero hmeas hint hmom]
  have hcoe : 𝓕 (⇑psi) = ⇑phi := by
    rw [← SchwartzMap.fourier_coe, hfp]
  rw [hzero, hcoe] at hswap
  have hmain : ∫ x : ℝ, G x • (phi x) = 0 := hswap.symm
  calc ∫ x : ℝ, g x • G x = ∫ x : ℝ, G x • (phi x) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have hval : (phi : ℝ → ℂ) x = (g x : ℂ) := rfl
        show g x • G x = G x • phi x
        rw [hval, smul_eq_mul, Complex.real_smul, mul_comm]
    _ = 0 := hmain

end

end Brockian.Moments

