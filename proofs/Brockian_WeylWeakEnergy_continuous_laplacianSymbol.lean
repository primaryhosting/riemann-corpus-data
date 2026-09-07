/-
  Brockian/WeylWeakEnergy.lean

  Fourier-energy uniqueness for non-real weak Schrodinger solutions.
-/
import Brockian.WeylWeakRegularityClosed
import Brockian.WeylWeakPrimitiveClassical

open MeasureTheory Complex
open scoped ENNReal SchwartzMap Laplacian

namespace Brockian.WeylWeakEnergy

open Brockian.WeylWeakRegularityScaffold
open Brockian.WeylWeakPrimitiveClassical
open Brockian.WeylWeakRegularityClosed
open Brockian.Weyl.SchrodingerMinimal

/-- A flattening-stable name for the one-dimensional complex `L2` space. -/
noncomputable abbrev L2R : Type :=
  Brockian.WeylWeakRegularityClosed.L2R

/-- The real Fourier symbol of the one-dimensional Laplacian, with Mathlib's
Fourier normalization. -/
noncomputable def laplacianSymbol (xi : Real) : Complex :=
  -((2 * Real.pi) ^ 2 : Complex) * Complex.ofReal (norm xi ^ 2)

theorem continuous_laplacianSymbol : Continuous laplacianSymbol := by
  unfold laplacianSymbol
  fun_prop

/-- Multiplication of an `L2` function by the Laplacian symbol remains locally
integrable, which is enough to identify it from its tempered distribution. -/
theorem laplacianSymbol_mul_locallyIntegrable (u : L2R) :
    LocallyIntegrable
      (fun xi => laplacianSymbol xi * ((FourierTransform.fourier u : L2R) : Real -> Complex) xi)
      volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  have hu : IntegrableOn
      ((FourierTransform.fourier u : L2R) : Real -> Complex) k volume :=
    ((Lp.memLp (FourierTransform.fourier u : L2R)).locallyIntegrable
      (by norm_num)).integrableOn_isCompact hk
  exact MeasureTheory.IntegrableOn.continuousOn_mul
    continuous_laplacianSymbol.continuousOn hu hk

/-- Distributional equality `Delta u = f` for `L2` functions gives the expected
a.e. Fourier multiplier identity. -/
theorem fourier_laplacian_ae
    (u f : L2R)
    (hDelta : Laplacian.laplacian (u : TemperedDistribution Real Complex) =
      (f : TemperedDistribution Real Complex)) :
    ∀ᵐ xi ∂volume,
      ((FourierTransform.fourier f : L2R) : Real -> Complex) xi =
        laplacianSymbol xi *
          ((FourierTransform.fourier u : L2R) : Real -> Complex) xi := by
  have hFourier :
      FourierTransform.fourier
          (Laplacian.laplacian (u : TemperedDistribution Real Complex)) =
        FourierTransform.fourier (f : TemperedDistribution Real Complex) :=
    congrArg (fun w : TemperedDistribution Real Complex => FourierTransform.fourier w) hDelta
  rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM,
    TemperedDistribution.fourierMultiplierCLM_apply] at hFourier
  have hsmul (c : Complex) (w : TemperedDistribution Real Complex) :
      FourierTransform.fourier (c • w) =
        c • FourierTransform.fourier w :=
    FourierSMul.fourier_smul c w
  have hinv (w : TemperedDistribution Real Complex) :
      FourierTransform.fourier (FourierTransform.fourierInv w) = w :=
    FourierInvPair.fourier_fourierInv_eq w
  rw [Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq,
    RCLike.real_smul_eq_coe_smul (K := Complex), hsmul, hinv] at hFourier
  have htg : Function.HasTemperateGrowth
      (fun x : Real => ((norm x ^ 2 : Real) : Complex)) := by
    have hconst : Function.HasTemperateGrowth
        (fun _ : Real => (1 : Complex)) :=
      Function.HasTemperateGrowth.const 1
    convert Function.HasTemperateGrowth.smul
      (Function.hasTemperateGrowth_norm_sq Real) hconst using 1
    funext x
    simp [Pi.smul_apply, RCLike.real_smul_eq_coe_smul]
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (FourierTransform.fourier f : L2R)).locallyIntegrable (by norm_num)
  · exact laplacianSymbol_mul_locallyIntegrable u
  · intro psi hpsi hsupp
    have hcompact : HasCompactSupport (Complex.ofRealCLM ∘ psi) :=
      hsupp.comp_left rfl
    have hsmooth := Complex.ofRealCLM.contDiff.comp hpsi
    let phi : SchwartzMap Real Complex := hcompact.toSchwartzMap hsmooth
    have hphi (x : Real) : phi x = Complex.ofReal (psi x) := rfl
    have hmul (x : Real) :
        (SchwartzMap.smulLeftCLM Complex
          (fun y : Real => ((norm y ^ 2 : Real) : Complex)) phi) x =
          ((norm x ^ 2 : Real) : Complex) * phi x := by
      simpa only [smul_eq_mul] using
        SchwartzMap.smulLeftCLM_apply_apply htg phi x
    have hconstIntegral (c : Complex) (r : Real -> Complex) :
        MeasureTheory.integral volume (fun x => c * r x) =
          c * MeasureTheory.integral volume r :=
      integral_const_mul c r
    have heval := congrArg (fun w : TemperedDistribution Real Complex => w phi) hFourier
    simp only [smul_apply, Pi.smul_apply,
      TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] at heval
    have hIntMul : MeasureTheory.integral volume (fun x =>
        (SchwartzMap.smulLeftCLM Complex
          (fun y : Real => ((norm y ^ 2 : Real) : Complex)) phi) x *
            ((FourierTransform.fourier u : L2R) : Real -> Complex) x) =
        MeasureTheory.integral volume (fun x =>
          (((norm x ^ 2 : Real) : Complex) * phi x) *
            ((FourierTransform.fourier u : L2R) : Real -> Complex) x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [hmul]
    have heval' := heval.symm
    rw [hIntMul] at heval'
    simp only [hphi] at heval'
    calc
      MeasureTheory.integral volume (fun x =>
          psi x • ((FourierTransform.fourier f : L2R) : Real -> Complex) x) =
          MeasureTheory.integral volume (fun x =>
            Complex.ofReal (psi x) *
              ((FourierTransform.fourier f : L2R) : Real -> Complex) x) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            exact RCLike.real_smul_eq_coe_smul (K := Complex) _ _
      _ =
          ((-(2 * Real.pi) ^ 2 : Real) : Complex) *
            MeasureTheory.integral volume (fun x =>
              (((norm x ^ 2 : Real) : Complex) * Complex.ofReal (psi x)) *
                ((FourierTransform.fourier u : L2R) : Real -> Complex) x) := by
            exact heval'
      _ = MeasureTheory.integral volume (fun x =>
          ((-(2 * Real.pi) ^ 2 : Real) : Complex) *
            ((((norm x ^ 2 : Real) : Complex) * Complex.ofReal (psi x)) *
              ((FourierTransform.fourier u : L2R) : Real -> Complex) x)) :=
        (hconstIntegral _ _).symm
      _ = MeasureTheory.integral volume (fun x =>
          psi x • (laplacianSymbol x *
            ((FourierTransform.fourier u : L2R) : Real -> Complex) x)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp only [laplacianSymbol, real_smul, smul_eq_mul]
        push_cast
        ring

/-- The expectation of a distributional Laplacian represented in `L2` is real. -/
theorem im_inner_laplacian_eq_zero
    (u f : L2R)
    (hDelta : Laplacian.laplacian (u : TemperedDistribution Real Complex) =
      (f : TemperedDistribution Real Complex)) :
    Complex.im ⟪u, f⟫_ℂ = 0 := by
  rw [← Lp.inner_fourier_eq u f, L2.inner_def]
  change RCLike.im (MeasureTheory.integral volume (fun x =>
    ⟪((FourierTransform.fourier u : L2R) : Real -> Complex) x,
      ((FourierTransform.fourier f : L2R) : Real -> Complex) x⟫_ℂ)) = 0
  rw [← integral_im
    (L2.integrable_inner (FourierTransform.fourier u : L2R)
      (FourierTransform.fourier f : L2R))]
  apply integral_eq_zero_of_ae
  filter_upwards [fourier_laplacian_ae u f hDelta] with xi hxi
  rw [hxi]
  simp only [RCLike.inner_apply']
  let q : Complex :=
    ((FourierTransform.fourier u : L2R) : Real -> Complex) xi
  change (conj q * (laplacianSymbol xi * q)).im = 0
  calc
    (conj q * (laplacianSymbol xi * q)).im =
        (laplacianSymbol xi * (conj q * q)).im := by ring
    _ = (laplacianSymbol xi * (Complex.normSq q : Complex)).im := by
      rw [Complex.normSq_eq_conj_mul_self]
    _ = 0 := by
      have hsymIm : (laplacianSymbol xi).im = 0 := by
        simp [laplacianSymbol, Complex.mul_im, pow_two,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [Complex.mul_im, hsymIm, Complex.ofReal_re, Complex.ofReal_im]
      ring

/-- The bounded real-potential operator acts by pointwise multiplication on an
arbitrary `L2` element. -/
theorem potentialMulCLM_coeFn
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) (u : L2R) :
    (potentialMulCLM V hVc M hV u : Real -> Complex) =ᵐ[volume]
      fun x => (V x : Complex) * (u : Real -> Complex) x := by
  unfold potentialMulCLM
  filter_upwards [coeFn_mulLpCLM _ _ _ _ u] with x hx
  simpa only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using hx

/-- The conjugated weak-equation right-hand side is exactly `V u - conj(z) u`
as an equality in `L2`. -/
theorem conjugateRHSLp_eq_potential_sub
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) (z : Complex) (g : L2R) :
    conjugateRHSLp V hVc z g hV =
      potentialMulCLM V hVc M hV (conjugateLp g) -
        conj z • conjugateLp g := by
  apply Lp.ext
  filter_upwards [conjugateRHSLp_coeFn hVc hV,
    potentialMulCLM_coeFn V hVc M hV (conjugateLp g),
    conjugateLp_coeFn g,
    Lp.coeFn_sub (potentialMulCLM V hVc M hV (conjugateLp g))
      (conj z • conjugateLp g),
    Lp.coeFn_smul (conj z) (conjugateLp g)] with x hrhs hmul hu hsub hsmul
  rw [hrhs, hsub]
  simp only [Pi.sub_apply]
  rw [hmul, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hu]
  simp only [conjugateRHS, conjugateRepresentative, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The imaginary part of the weak right-hand side is entirely contributed by
the non-real spectral parameter; the real potential contributes zero. -/
theorem im_inner_conjugateRHSLp
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) (z : Complex) (g : L2R) :
    Complex.im ⟪conjugateLp g, conjugateRHSLp V hVc z g hV⟫_ℂ =
      z.im * norm (conjugateLp g) ^ 2 := by
  rw [conjugateRHSLp_eq_potential_sub V hVc M hV z g,
    inner_sub_right, inner_smul_right]
  have hsymm :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_potentialMulCLM V hVc M hV)
  have hpot : Complex.im
      ⟪conjugateLp g, potentialMulCLM V hVc M hV (conjugateLp g)⟫_ℂ = 0 :=
    hsymm.im_inner_self_apply (conjugateLp g)
  rw [Complex.sub_im, hpot, zero_sub]
  rw [inner_self_eq_norm_sq_to_K]
  change -(conj z * (norm (conjugateLp g) ^ 2 : Complex)).im =
    z.im * norm (conjugateLp g) ^ 2
  simp [Complex.mul_im, pow_two]

/-- `conjugateLp` is the involutive star operation on complex `L2`. -/
theorem conjugateLp_eq_star (g : L2R) : conjugateLp g = star g := by
  apply Lp.ext
  filter_upwards [conjugateLp_coeFn g, Lp.coeFn_star g] with x hu hs
  rw [hu, hs]
  rfl

/-- Every non-real weak `L2` solution for a continuous bounded real potential
vanishes.  This is the energy-identity replacement for pointwise weak-to-
classical regularity. -/
theorem weakSolutionVanishing_of_continuous_bounded
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    WeakSolutionVanishing V := by
  intro z hz g hweak
  let u : L2R := conjugateLp g
  let f : L2R := conjugateRHSLp V hVc z g hV
  have hDelta : Laplacian.laplacian (u : TemperedDistribution Real Complex) =
      (f : TemperedDistribution Real Complex) := by
    exact (laplacian_eq_secondDeriv
      (conjugateLp g : TemperedDistribution Real Complex)).trans
        (secondDeriv_conjugateLp_eq_conjugateRHSLp V hVc hV z g hweak)
  have hreal : Complex.im ⟪u, f⟫_ℂ = 0 :=
    im_inner_laplacian_eq_zero u f hDelta
  have him : Complex.im ⟪u, f⟫_ℂ = z.im * norm u ^ 2 := by
    exact im_inner_conjugateRHSLp V hVc M hV z g
  have hnormSq : norm u ^ 2 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hz
    rw [← him]
    exact hreal
  have hnorm : norm u = 0 := by
    apply mul_self_eq_zero.mp
    simpa only [pow_two] using hnormSq
  have hu : u = 0 := norm_eq_zero.mp hnorm
  have hconjZero : conjugateLp g = 0 := by
    simpa [u] using hu
  have hrep := conjugateLp_coeFn g
  rw [hconjZero] at hrep
  apply Lp.ext
  filter_upwards [hrep,
    Lp.coeFn_zero (E := Complex) (p := (2 : ENNReal))
      (μ := (volume : Measure Real))] with x hrepX hzeroX
  rw [hzeroX] at hrepX ⊢
  have hc : conj ((g : Real -> Complex) x) = 0 := by
    simpa [conjugateRepresentative] using hrepX.symm
  have hcc := congrArg conj hc
  simpa using hcc

/-- Gate 1 for the concrete minimal Schrodinger operator, with no regularity or
resolvent hypothesis left: continuous bounded real potentials give an
essentially self-adjoint Schwartz-core operator. -/
theorem schrodinger_essentiallySelfAdjoint_of_continuous_bounded
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    Brockian.Weyl.Operator.EssentiallySelfAdjoint
      (schrodingerPMap V hVc M hV) :=
  Brockian.WeylWeakRegularityDischarge.schrodinger_essentiallySelfAdjoint_of_weakToPrimitive
    V hVc M hV
      (weakToPrimitiveRegularity_of_weakSolutionVanishing
        (weakSolutionVanishing_of_continuous_bounded V hVc M hV))

end Brockian.WeylWeakEnergy
