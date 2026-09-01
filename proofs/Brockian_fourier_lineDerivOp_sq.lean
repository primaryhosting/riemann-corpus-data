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
# The Fourier transform of the Laplacian on Schwartz space

We record the classical formula `𝓕 (Δ f) ξ = -(4π²‖ξ‖²) 𝓕 f ξ` for Schwartz functions,
introduce the Fourier symbol `freeSymbol ξ = 4π²‖ξ‖²` of the free Laplacian `-Δ`, and show that
the "resolvent multiplier" `ξ ↦ (1 + freeSymbol ξ)⁻¹` has temperate growth (so that multiplying
a Schwartz function by it produces again a Schwartz function).
-/

namespace Brockian

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem fourier_lineDerivOp_sq (f : 𝓢(V, ℂ)) (m : V) (ξ : V) :
    𝓕 (lineDerivOp m (lineDerivOp m f)) ξ
      = (2 * π * Complex.I) ^ 2 * ((inner ℝ ξ m : ℝ) : ℂ) ^ 2 * 𝓕 f ξ := by
  have h : (inner ℝ · m).HasTemperateGrowth (E := V) := ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  simp [smulLeftCLM_apply_apply h]
  ring

/-- The Fourier transform turns the Laplacian into multiplication by `-4π²‖ξ‖²`. -/
theorem fourier_laplacian (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (laplacianCLM ℂ V 𝓢(V, ℂ) f) ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  rw [laplacianCLM_eq, SchwartzMap.laplacian_eq_sum b, ← fourierTransformCLM_apply (𝕜 := ℂ),
    map_sum]
  simp only [SchwartzMap.sum_apply, fourierTransformCLM_apply]
  rw [Finset.sum_congr rfl (fun i _ => fourier_lineDerivOp_sq f (b i) ξ)]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have key : ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← OrthonormalBasis.sum_sq_inner_left b ξ]
    push_cast
    ring
  rw [key]
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The Fourier symbol of the free Laplacian `-Δ`. -/
def freeSymbol (ξ : V) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem freeSymbol_nonneg (ξ : V) : 0 ≤ freeSymbol ξ := by
  unfold freeSymbol; positivity

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem continuous_freeSymbol : Continuous (freeSymbol : V → ℝ) := by
  unfold freeSymbol; fun_prop

/-- The Fourier transform of `-Δ f` is multiplication by the symbol. -/
theorem fourier_neg_laplacian (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (-(laplacianCLM ℂ V 𝓢(V, ℂ) f)) ξ = (freeSymbol ξ : ℂ) * 𝓕 f ξ := by
  have : 𝓕 (-(laplacianCLM ℂ V 𝓢(V, ℂ) f)) = -𝓕 (laplacianCLM ℂ V 𝓢(V, ℂ) f) := by
    rw [← fourierTransformCLM_apply (𝕜 := ℂ), ← fourierTransformCLM_apply (𝕜 := ℂ), map_neg]
  rw [this]
  simp only [SchwartzMap.neg_apply, fourier_laplacian f ξ, freeSymbol]
  push_cast
  ring

/-- The resolvent multiplier `(1 + freeSymbol)⁻¹`, as a complex-valued function. -/
def freeResolventSymbol (ξ : V) : ℂ := ((1 + freeSymbol ξ)⁻¹ : ℝ)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem one_add_freeSymbol_pos (ξ : V) : 0 < 1 + freeSymbol ξ := by
  have := freeSymbol_nonneg ξ; linarith

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem hasTemperateGrowth_freeResolventSymbol :
    Function.HasTemperateGrowth (freeResolventSymbol : V → ℂ) := by
  have hscale : Function.HasTemperateGrowth (fun ξ : V => (2 * π : ℝ) • ξ) := by
    have := ((2 * π : ℝ) • ContinuousLinearMap.id ℝ V).hasTemperateGrowth
    simpa using this
  have hb : Function.HasTemperateGrowth (fun y : V => (1 + ‖y‖ ^ 2) ^ (-1 : ℝ)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow V (-1)
  have hcomp : Function.HasTemperateGrowth (fun ξ : V => (1 + ‖(2 * π : ℝ) • ξ‖ ^ 2) ^ (-1 : ℝ)) :=
    hb.comp hscale
  have heq : (fun ξ : V => (1 + ‖(2 * π : ℝ) • ξ‖ ^ 2) ^ (-1 : ℝ))
      = (fun ξ : V => (1 + freeSymbol ξ)⁻¹) := by
    funext ξ
    rw [Real.rpow_neg_one, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    congr 1
    simp only [freeSymbol, mul_pow]
    ring
  rw [heq] at hcomp
  have h2 := Function.HasTemperateGrowth.comp Function.Complex.hasTemperateGrowth_ofReal hcomp
  have h3 : (Complex.ofReal ∘ fun ξ : V => (1 + freeSymbol ξ)⁻¹) = (freeResolventSymbol : V → ℂ) :=
    rfl
  rwa [h3] at h2

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_freeResolventSymbol_le_one (ξ : V) : ‖(freeResolventSymbol ξ : ℂ)‖ ≤ 1 := by
  have h := one_add_freeSymbol_pos (V := V) ξ
  rw [freeResolventSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [inv_le_one_iff₀]
  right
  have := freeSymbol_nonneg (V := V) ξ
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_freeSymbol_mul_freeResolventSymbol_le_one (ξ : V) :
    ‖(freeSymbol ξ : ℂ) * freeResolventSymbol ξ‖ ≤ 1 := by
  have h := one_add_freeSymbol_pos (V := V) ξ
  have h0 := freeSymbol_nonneg (V := V) ξ
  rw [freeResolventSymbol, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  rw [mul_inv_le_iff₀ h, one_mul]
  linarith

end

end Brockian

import Mathlib

/-!
# Multiplication operators on `L²`

For a real-valued continuous function `m` on a finite-dimensional real inner product space `V`
we define the (maximal) multiplication operator `mulOp m` on `L²(V; ℂ)` as an unbounded operator
(a `LinearPMap`), with domain all `u ∈ L²` such that `m * u ∈ L²`.

The main result is `Brockian.mulOp_isSelfAdjoint`: such a multiplication operator is
self-adjoint.
-/

namespace Brockian

open MeasureTheory Filter
open scoped ENNReal ComplexInnerProductSpace Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The complex `L²` space of a finite-dimensional real inner product space, with respect to
the Lebesgue (volume) measure. -/
abbrev L2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] := Lp (α := V) ℂ 2 (volume : Measure V)

/-- A pointwise a.e. bound `‖b x‖ ≤ C` on a multiplier gives the corresponding bound on
`L²`-norms. -/
theorem norm_le_of_ae_mul {C : ℝ} (hC : 0 ≤ C) {b : V → ℂ} {u w : L2 V}
    (hb : ∀ᵐ x ∂(volume : Measure V), ‖b x‖ ≤ C)
    (h : (w : V → ℂ) =ᵐ[volume] fun x => b x * (u : V → ℂ) x) : ‖w‖ ≤ C * ‖u‖ := by
  have h2 : ∀ᵐ x ∂(volume : Measure V),
      ‖(w : V → ℂ) x‖ ≤ ‖((C : ℝ) • u : L2 V) x‖ := by
    filter_upwards [h, hb, Lp.coeFn_smul (C : ℝ) u] with x hx hbx hsx
    rw [hx, hsx]
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_mul]
    exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)
  have := MeasureTheory.Lp.norm_le_norm_of_ae_le h2
  simpa [norm_smul, abs_of_nonneg hC] using this

section mul

variable (m : V → ℝ)

/-- The maximal domain of the multiplication operator by `m` inside `L²`. -/
def mulDomain : Submodule ℂ (L2 V) where
  carrier := {u : L2 V | MemLp (fun x => (m x : ℂ) * (u : V → ℂ) x) 2 (volume : Measure V)}
  add_mem' := by
    intro u v hu hv
    refine (MemLp.add hu hv).ae_eq ?_
    filter_upwards [Lp.coeFn_add u v] with x hx
    simp only [Pi.add_apply] at hx ⊢
    rw [hx]; ring
  zero_mem' := by
    refine (MemLp.zero (p := 2) (μ := (volume : Measure V)) (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure V)] with x hx
    simp
  smul_mem' := by
    intro c u hu
    refine (MemLp.const_smul hu c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]; ring

theorem mem_mulDomain_iff (u : L2 V) :
    u ∈ mulDomain m ↔ MemLp (fun x => (m x : ℂ) * (u : V → ℂ) x) 2 (volume : Measure V) :=
  Iff.rfl

/-- The function underlying the multiplication operator. -/
def mulFun (u : mulDomain m) : L2 V := MemLp.toLp _ u.2

theorem coeFn_mulFun (u : mulDomain m) :
    ((mulFun m u : L2 V) : V → ℂ) =ᵐ[volume] fun x => (m x : ℂ) * ((u : L2 V) : V → ℂ) x :=
  MemLp.coeFn_toLp u.2

/-- The multiplication operator by a real-valued function `m`, as an unbounded operator on
`L²(V; ℂ)` with maximal domain. -/
def mulOp : L2 V →ₗ.[ℂ] L2 V where
  domain := mulDomain m
  toFun :=
    { toFun := mulFun m
      map_add' := by
        intro u v
        refine Lp.ext ?_
        filter_upwards [coeFn_mulFun m (u + v), coeFn_mulFun m u, coeFn_mulFun m v,
          Lp.coeFn_add (mulFun m u) (mulFun m v), Lp.coeFn_add (u : L2 V) (v : L2 V)]
          with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at *
        rw [h1, h4, h2, h3,
          show ((u + v : mulDomain m) : L2 V) = (u : L2 V) + (v : L2 V) from rfl, h5]
        ring
      map_smul' := by
        intro c u
        refine Lp.ext ?_
        filter_upwards [coeFn_mulFun m (c • u), coeFn_mulFun m u,
          Lp.coeFn_smul c (mulFun m u), Lp.coeFn_smul c (u : L2 V)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
        rw [h1, h3, h2,
          show ((c • u : mulDomain m) : L2 V) = c • (u : L2 V) from rfl, h4]
        ring }

@[simp] theorem mulOp_domain : (mulOp m).domain = mulDomain m := rfl

theorem coeFn_mulOp (u : (mulOp m).domain) :
    ((mulOp m u : L2 V) : V → ℂ) =ᵐ[volume] fun x => (m x : ℂ) * ((u : L2 V) : V → ℂ) x :=
  coeFn_mulFun m u

/-- Characterisation of the value of the multiplication operator. -/
theorem mulOp_eq_of_ae (u : (mulOp m).domain) (w : L2 V)
    (h : (w : V → ℂ) =ᵐ[volume] fun x => (m x : ℂ) * ((u : L2 V) : V → ℂ) x) :
    mulOp m u = w :=
  Lp.ext ((coeFn_mulOp m u).trans h.symm)

variable (hm : Continuous m)
include hm

omit hm in
theorem mulOp_isFormalAdjoint : (mulOp m).IsFormalAdjoint (mulOp m) := by
  intro u v
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulOp m u, coeFn_mulOp m v] with a h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- **Multiplication operators are self-adjoint**, provided their (maximal) domain is dense. -/
theorem mulOp_isSelfAdjoint (hd : Dense ((mulOp m).domain : Set (L2 V))) :
    IsSelfAdjoint (mulOp m) := by
  have hdom : ((mulOp m).adjoint).domain ≤ (mulOp m).domain := by
    intro y hy
    set w : L2 V := (mulOp m).adjoint ⟨y, hy⟩ with hw
    have hadj : ∀ x : (mulOp m).domain, inner ℂ w (x : L2 V) = inner ℂ y ((mulOp m) x) :=
      fun x => LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ x
    set v : V → ℂ := ((y : L2 V) : V → ℂ) with hv
    have hvLp : MemLp v 2 (volume : Measure V) := Lp.memLp y
    have hvmeas : AEStronglyMeasurable v (volume : Measure V) := hvLp.1
    have hmc : AEStronglyMeasurable (fun x => (m x : ℂ)) (volume : Measure V) :=
      (Complex.continuous_ofReal.comp hm).aestronglyMeasurable
    set S : ℕ → Set V := fun n => {x | |m x| ≤ (n : ℝ)} with hS
    have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
      measurableSet_le (hm.abs.measurable) measurable_const
    set g : ℕ → V → ℂ := fun n => (S n).indicator (fun x => (m x : ℂ) * v x) with hg
    have hgmeas : ∀ n, AEStronglyMeasurable (g n) (volume : Measure V) := fun n =>
      (hmc.mul hvmeas).indicator (hSmeas n)
    have hgbound : ∀ n x, ‖g n x‖ ≤ ‖(((n : ℝ) : ℂ)) * v x‖ := by
      intro n x
      have hrhs : ‖(((n : ℝ) : ℂ)) * v x‖ = (n : ℝ) * ‖v x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
      rw [hrhs]
      by_cases hx : x ∈ S n
      · have hga : g n x = (m x : ℂ) * v x := by simp [hg, Set.indicator_of_mem hx]
        have hmn : |m x| ≤ (n : ℝ) := hx
        rw [hga, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hmn (norm_nonneg _)
      · have hga : g n x = 0 := by simp [hg, Set.indicator_of_notMem hx]
        rw [hga, norm_zero]
        positivity
    have hgLp : ∀ n, MemLp (g n) 2 (volume : Measure V) := fun n =>
      MemLp.of_le (hvLp.const_mul ((n : ℝ) : ℂ)) (hgmeas n)
        (Filter.Eventually.of_forall (hgbound n))
    set xn : ℕ → L2 V := fun n => (hgLp n).toLp (g n) with hxn
    have hxncoe : ∀ n, ((xn n : L2 V) : V → ℂ) =ᵐ[volume] g n := fun n => MemLp.coeFn_toLp _
    have hxnmem : ∀ n, xn n ∈ (mulOp m).domain := by
      intro n
      have hbound : ∀ x, ‖(m x : ℂ) * g n x‖ ≤ ‖(((n : ℝ) ^ 2 : ℝ) : ℂ) * v x‖ := by
        intro x
        have hrhs : ‖(((n : ℝ) ^ 2 : ℝ) : ℂ) * v x‖ = ((n : ℝ) ^ 2) * ‖v x‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ 2)]
        rw [hrhs]
        by_cases hx : x ∈ S n
        · have hga : g n x = (m x : ℂ) * v x := by simp [hg, Set.indicator_of_mem hx]
          have hmn : |m x| ≤ (n : ℝ) := hx
          have h3 : |m x * m x| ≤ (n : ℝ) ^ 2 := by
            rw [abs_mul]
            nlinarith [abs_nonneg (m x)]
          rw [hga, ← mul_assoc, ← Complex.ofReal_mul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        · have hga : g n x = 0 := by simp [hg, Set.indicator_of_notMem hx]
          rw [hga, mul_zero, norm_zero]
          positivity
      have hmem : MemLp (fun x => (m x : ℂ) * g n x) 2 (volume : Measure V) :=
        MemLp.of_le (hvLp.const_mul (((n : ℝ) ^ 2 : ℝ) : ℂ)) (hmc.mul (hgmeas n))
          (Filter.Eventually.of_forall hbound)
      show MemLp (fun x => (m x : ℂ) * ((xn n : L2 V) : V → ℂ) x) 2 (volume : Measure V)
      refine hmem.ae_eq ?_
      filter_upwards [hxncoe n] with x hx
      rw [hx]
    have hnorm : ∀ n, ‖xn n‖ ≤ ‖w‖ := by
      intro n
      have hinner : inner ℂ (y : L2 V) ((mulOp m) ⟨xn n, hxnmem n⟩)
          = inner ℂ (xn n : L2 V) (xn n : L2 V) := by
        rw [L2.inner_def, L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_mulOp m ⟨xn n, hxnmem n⟩, hxncoe n] with a h1 h2
        rw [h1, h2]
        by_cases hx : a ∈ S n
        · have hga : g n a = (m a : ℂ) * v a := by simp [hg, Set.indicator_of_mem hx]
          rw [hga]
          simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
          ring
        · have hga : g n a = 0 := by simp [hg, Set.indicator_of_notMem hx]
          rw [hga]
          simp [RCLike.inner_apply]
      have h1 : ((‖xn n‖ : ℂ)) ^ 2 = inner ℂ w (xn n : L2 V) := by
        rw [hadj ⟨xn n, hxnmem n⟩, hinner, inner_self_eq_norm_sq_to_K]
        norm_cast
      have h2 : ‖xn n‖ ^ 2 ≤ ‖w‖ * ‖xn n‖ := by
        have := congrArg Norm.norm h1
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
        rw [this]
        exact norm_inner_le_norm (𝕜 := ℂ) w (xn n : L2 V)
      rcases eq_or_lt_of_le (norm_nonneg (xn n)) with h0 | h0
      · rw [← h0]; exact norm_nonneg _
      · exact le_of_mul_le_mul_right (by nlinarith) h0
    -- pass to the limit
    have hlim : ∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (nhds ((m x : ℂ) * v x)) := by
      intro x
      obtain ⟨N, hN⟩ := exists_nat_ge |m x|
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hx : x ∈ S n := le_trans hN (by exact_mod_cast hn)
      simp [hg, Set.indicator_of_mem hx]
    have heLp : ∀ n, eLpNorm (g n) 2 (volume : Measure V) ≤ ENNReal.ofReal ‖w‖ := by
      intro n
      have hfin : eLpNorm (g n) 2 (volume : Measure V) ≠ ⊤ := (hgLp n).2.ne
      have hn : (eLpNorm (g n) 2 (volume : Measure V)).toReal ≤ ‖w‖ := by
        have := hnorm n
        rwa [Lp.norm_def, eLpNorm_congr_ae (hxncoe n)] at this
      calc eLpNorm (g n) 2 (volume : Measure V)
          = ENNReal.ofReal (eLpNorm (g n) 2 (volume : Measure V)).toReal := by
            rw [ENNReal.ofReal_toReal hfin]
        _ ≤ ENNReal.ofReal ‖w‖ := ENNReal.ofReal_le_ofReal hn
    have hfinal : eLpNorm (fun x => (m x : ℂ) * v x) 2 (volume : Measure V)
        ≤ ENNReal.ofReal ‖w‖ :=
      MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall heLp) hgmeas
        (Filter.Eventually.of_forall hlim)
    exact ⟨hmc.mul hvmeas, lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top⟩
  have hle : (mulOp m).adjoint ≤ mulOp m := by
    refine ⟨hdom, ?_⟩
    intro p q hpq
    refine hd.eq_of_inner_left ?_
    intro z
    have h1 : inner ℂ ((mulOp m).adjoint p) (z : L2 V) = inner ℂ (p : L2 V) ((mulOp m) z) :=
      LinearPMap.adjoint_isFormalAdjoint hd p z
    have h2 : inner ℂ ((mulOp m) q) (z : L2 V) = inner ℂ (q : L2 V) ((mulOp m) z) :=
      mulOp_isFormalAdjoint m q z
    rw [h1, h2, hpq]
  exact le_antisymm hle (LinearPMap.IsFormalAdjoint.le_adjoint hd (mulOp_isFormalAdjoint m))

end mul

end

end Brockian

import Brockian.MultiplicationOperator
import Brockian.SchwartzFourierLaplacian

/-!
# The Laplacian on the Schwartz core

We embed the Schwartz space into `L²(V; ℂ)` and define `negLaplacianCore`, the operator `-Δ`
with domain the (dense) subspace of Schwartz functions.
-/

namespace Brockian

open MeasureTheory SchwartzMap Filter LinearPMap LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The embedding of the Schwartz space into `L²`. -/
def schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V := (toLpCLM ℂ ℂ 2 (volume : Measure V)).toLinearMap

@[simp] theorem schwartzToL2_apply (f : 𝓢(V, ℂ)) :
    (schwartzToL2 f : L2 V) = f.toLp 2 (volume : Measure V) := rfl

theorem schwartzToL2_injective : Function.Injective (schwartzToL2 : 𝓢(V, ℂ) → L2 V) := by
  intro f g h
  have h1 : (f : V → ℂ) =ᵐ[volume] (g : V → ℂ) := by
    have hf := SchwartzMap.coeFn_toLp (μ := (volume : Measure V)) (p := 2) f
    have hg := SchwartzMap.coeFn_toLp (μ := (volume : Measure V)) (p := 2) g
    rw [show (f.toLp 2 (volume : Measure V)) = g.toLp 2 (volume : Measure V) from h] at hf
    exact hf.symm.trans hg
  exact SchwartzMap.ext
    (congrFun ((Continuous.ae_eq_iff_eq (volume : Measure V) f.continuous g.continuous).mp h1))

/-- `-Δ` acting on Schwartz functions. -/
def negLaplacianSchwartz : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) :=
  -(laplacianCLM ℂ V 𝓢(V, ℂ)).toLinearMap

omit [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem negLaplacianSchwartz_apply (f : 𝓢(V, ℂ)) :
    negLaplacianSchwartz f = -(laplacianCLM ℂ V 𝓢(V, ℂ) f) := rfl

/-- The free Laplacian `-Δ` defined on the core of Schwartz functions, as an unbounded operator
on `L²(V; ℂ)`. -/
def negLaplacianCore : L2 V →ₗ.[ℂ] L2 V where
  domain := LinearMap.range (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V)
  toFun := (schwartzToL2 ∘ₗ negLaplacianSchwartz) ∘ₗ
    (LinearEquiv.ofInjective _ schwartzToL2_injective).symm.toLinearMap

theorem mem_negLaplacianCore_domain (f : 𝓢(V, ℂ)) :
    (schwartzToL2 f : L2 V) ∈ (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).domain :=
  ⟨f, rfl⟩

theorem negLaplacianCore_apply (f : 𝓢(V, ℂ)) :
    negLaplacianCore (⟨schwartzToL2 f, mem_negLaplacianCore_domain f⟩ :
      (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).domain)
      = schwartzToL2 (negLaplacianSchwartz f) := by
  have h : (LinearEquiv.ofInjective (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V)
      schwartzToL2_injective).symm ⟨schwartzToL2 f, mem_negLaplacianCore_domain f⟩ = f := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  show (schwartzToL2 ∘ₗ negLaplacianSchwartz) ((LinearEquiv.ofInjective
    (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V) schwartzToL2_injective).symm
      ⟨schwartzToL2 f, mem_negLaplacianCore_domain f⟩) = _
  rw [h]
  rfl

theorem dense_negLaplacianCore_domain :
    Dense (((negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).domain : Submodule ℂ (L2 V)) : Set (L2 V)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
    (μ := (volume : Measure V))
  have : ((LinearMap.range (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V) : Submodule ℂ (L2 V)) : Set (L2 V))
      = Set.range (fun f : 𝓢(V, ℂ) => f.toLp 2 (volume : Measure V)) := by
    ext x
    simp [LinearMap.mem_range, schwartzToL2]
  show Dense (((LinearMap.range (schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V)) : Submodule ℂ (L2 V)) :
    Set (L2 V))
  rw [this]
  exact h

end

end Brockian

import Mathlib

/-!
# Conjugation of unbounded operators by a unitary

If `U` is a unitary (a surjective linear isometry) of a Hilbert space `E` and `T` is an unbounded
operator on `E`, then `conjPMap U T = U⁻¹ ∘ T ∘ U` is again an unbounded operator, and taking
adjoints commutes with this conjugation.  In particular the conjugate of a self-adjoint operator
is self-adjoint.
-/

namespace Brockian

open LinearPMap

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The conjugate `U⁻¹ ∘ T ∘ U` of an unbounded operator `T` by a unitary `U`. -/
def conjPMap (U : E ≃ₗᵢ[𝕜] E) (T : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E where
  domain := T.domain.comap (U.toLinearEquiv : E →ₗ[𝕜] E)
  toFun := ((U.symm.toLinearEquiv : E →ₗ[𝕜] E) ∘ₗ T.toFun) ∘ₗ
    ((U.toLinearEquiv : E →ₗ[𝕜] E).restrict
      (p := T.domain.comap (U.toLinearEquiv : E →ₗ[𝕜] E)) (q := T.domain) (fun _ hx => hx))

variable (U : E ≃ₗᵢ[𝕜] E) (T : E →ₗ.[𝕜] E)

omit [CompleteSpace E] in
@[simp] theorem mem_conjPMap_domain {x : E} : x ∈ (conjPMap U T).domain ↔ U x ∈ T.domain :=
  Iff.rfl

omit [CompleteSpace E] in
theorem conjPMap_apply (u : (conjPMap U T).domain) (h : U (u : E) ∈ T.domain) :
    conjPMap U T u = U.symm (T ⟨U (u : E), h⟩) := rfl

/-- The formal adjoint property, in the form `⟪T a, b⟫ = ⟪a, T† b⟫`. -/
theorem inner_apply_adjoint (hT : Dense (T.domain : Set E)) (a : T.domain)
    (b : T.adjoint.domain) : inner 𝕜 (T a) (b : E) = inner 𝕜 (a : E) (T.adjoint b) := by
  have h2 := congrArg (starRingEnd 𝕜) (LinearPMap.adjoint_isFormalAdjoint hT b a)
  rw [inner_conj_symm, inner_conj_symm] at h2
  exact h2.symm

omit [CompleteSpace E] in
theorem dense_conjPMap_domain (hT : Dense (T.domain : Set E)) :
    Dense (((conjPMap U T).domain : Submodule 𝕜 E) : Set E) := by
  have hset : (((conjPMap U T).domain : Submodule 𝕜 E) : Set E)
      = (U.symm.toHomeomorph) '' ((T.domain : Submodule 𝕜 E) : Set E) := by
    ext x
    constructor
    · intro hx
      exact ⟨U x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      show U (U.symm y) ∈ T.domain
      simpa using hy
  rw [hset, U.symm.toHomeomorph.isDenseEmbedding.dense_image]
  exact hT

/-- Taking adjoints commutes with unitary conjugation. -/
theorem conjPMap_adjoint (hT : Dense (T.domain : Set E)) :
    (conjPMap U T).adjoint = conjPMap U T.adjoint := by
  have hcd : Dense (((conjPMap U T).domain : Submodule 𝕜 E) : Set E) :=
    dense_conjPMap_domain U T hT
  refine le_antisymm ?_ ?_
  · have hdom : ((conjPMap U T).adjoint).domain ≤ (conjPMap U T.adjoint).domain := by
      intro y hy
      show U y ∈ T.adjoint.domain
      refine LinearPMap.mem_adjoint_domain_of_exists _
        ⟨U ((conjPMap U T).adjoint ⟨y, hy⟩), ?_⟩
      intro x
      have hx : U (U.symm (x : E)) ∈ T.domain := by simp
      have h1 := LinearPMap.adjoint_isFormalAdjoint hcd ⟨y, hy⟩ ⟨U.symm (x : E), hx⟩
      have hxx : (⟨U (U.symm (x : E)), hx⟩ : T.domain) = x := Subtype.ext (by simp)
      have h2 : conjPMap U T ⟨U.symm (x : E), hx⟩ = U.symm (T x) := by
        rw [conjPMap_apply U T ⟨U.symm (x : E), hx⟩ hx, hxx]
      rw [h2] at h1
      calc inner 𝕜 (U ((conjPMap U T).adjoint ⟨y, hy⟩)) (x : E)
          = inner 𝕜 ((conjPMap U T).adjoint ⟨y, hy⟩) (U.symm (x : E)) := by
            rw [← U.inner_map_map ((conjPMap U T).adjoint ⟨y, hy⟩) (U.symm (x : E))]
            simp
        _ = inner 𝕜 y (U.symm (T x)) := h1
        _ = inner 𝕜 (U y) (T x) := by
            rw [← U.inner_map_map y (U.symm (T x))]
            simp
    refine ⟨hdom, ?_⟩
    intro p q hpq
    have hq : U (q : E) ∈ T.adjoint.domain := q.2
    refine LinearPMap.adjoint_apply_eq hcd p ?_
    intro z
    have hz : U (z : E) ∈ T.domain := z.2
    have h1 : conjPMap U T.adjoint q = U.symm (T.adjoint ⟨U (q : E), hq⟩) := rfl
    calc inner 𝕜 (conjPMap U T.adjoint q) (z : E)
        = inner 𝕜 (U (q : E)) (T ⟨U (z : E), hz⟩) := by
          rw [h1, ← U.inner_map_map (U.symm (T.adjoint ⟨U (q : E), hq⟩)) (z : E)]
          simp only [LinearIsometryEquiv.apply_symm_apply]
          exact LinearPMap.adjoint_isFormalAdjoint hT ⟨U (q : E), hq⟩ ⟨U (z : E), hz⟩
      _ = inner 𝕜 (q : E) (conjPMap U T z) := by
          rw [conjPMap_apply U T z hz, ← U.inner_map_map (q : E) (U.symm (T ⟨U (z : E), hz⟩))]
          simp
      _ = inner 𝕜 (p : E) (conjPMap U T z) := by rw [hpq]
  · refine LinearPMap.IsFormalAdjoint.le_adjoint hcd ?_
    intro x y
    have hx : U (x : E) ∈ T.domain := x.2
    have hy : U (y : E) ∈ T.adjoint.domain := y.2
    have h1 : conjPMap U T x = U.symm (T ⟨U (x : E), hx⟩) := rfl
    have h2 : conjPMap U T.adjoint y = U.symm (T.adjoint ⟨U (y : E), hy⟩) := rfl
    rw [h1, h2]
    rw [show inner 𝕜 (U.symm (T ⟨U (x : E), hx⟩)) (y : E)
        = inner 𝕜 (T ⟨U (x : E), hx⟩) (U (y : E)) by
      rw [← U.inner_map_map (U.symm (T ⟨U (x : E), hx⟩)) (y : E)]
      simp]
    rw [show inner 𝕜 (x : E) (U.symm (T.adjoint ⟨U (y : E), hy⟩))
        = inner 𝕜 (U (x : E)) (T.adjoint ⟨U (y : E), hy⟩) by
      rw [← U.inner_map_map (x : E) (U.symm (T.adjoint ⟨U (y : E), hy⟩))]
      simp]
    exact inner_apply_adjoint T hT ⟨U (x : E), hx⟩ ⟨U (y : E), hy⟩

/-- The conjugate of a self-adjoint operator by a unitary is self-adjoint. -/
theorem conjPMap_isSelfAdjoint (hT : IsSelfAdjoint T) : IsSelfAdjoint (conjPMap U T) := by
  have hd : Dense (T.domain : Set E) := hT.dense_domain
  rw [LinearPMap.isSelfAdjoint_def] at hT ⊢
  rw [conjPMap_adjoint U T hd, hT]

/-- Taking adjoints is antitone. -/
theorem adjoint_le_adjoint {S T : E →ₗ.[𝕜] E} (hS : Dense (S.domain : Set E)) (h : S ≤ T) :
    T.adjoint ≤ S.adjoint := by
  have hT : Dense (T.domain : Set E) := hS.mono h.1
  refine LinearPMap.IsFormalAdjoint.le_adjoint hS ?_
  intro x y
  have hx : (x : E) ∈ T.domain := h.1 x.2
  have hSx : S x = T ⟨(x : E), hx⟩ := h.2 rfl
  rw [hSx]
  exact inner_apply_adjoint T hT ⟨(x : E), hx⟩ y

end

end Brockian

import Brockian.MultiplicationOperator
import Brockian.PMapConjugation
import Brockian.SchwartzFourierLaplacian
import Brockian.SchwartzCore

/-!
# Essential self-adjointness of the free Laplacian, via Plancherel

Let `V` be a finite-dimensional real inner product space and let `H = L²(V; ℂ)`.

We consider the *free Laplacian* `-Δ`, defined on the core of Schwartz functions
(`negLaplacianCore`), and the operator `freeLaplacian`, which is the conjugate under the
(unitary, by Plancherel) Fourier transform of the maximal multiplication operator by the symbol
`freeSymbol ξ = 4π²‖ξ‖²`.

The main theorem `freeLaplacian_essentiallySelfAdjoint_via_plancherel` states that `-Δ` defined
on Schwartz functions is *essentially self-adjoint*: its closure is self-adjoint, and it admits
exactly one self-adjoint extension.
-/

namespace Brockian

open MeasureTheory SchwartzMap Filter LinearPMap LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform as a unitary of `L²(V; ℂ)` (Plancherel's theorem). -/
abbrev fourierU (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] : L2 V ≃ₗᵢ[ℂ] L2 V := Lp.fourierTransformₗᵢ V ℂ

/-- The free Laplacian `-Δ` with its maximal domain, defined as the conjugate under the Fourier
transform of the multiplication operator by the symbol `4π²‖ξ‖²`. -/
def freeLaplacian : L2 V →ₗ.[ℂ] L2 V := conjPMap (fourierU V) (mulOp freeSymbol)

theorem fourierU_schwartzToL2 (f : 𝓢(V, ℂ)) :
    fourierU V (schwartzToL2 f) = schwartzToL2 (𝓕 f) :=
  SchwartzMap.toLp_fourier_eq f

theorem fourierU_symm_schwartzToL2 (f : 𝓢(V, ℂ)) :
    (fourierU V).symm (schwartzToL2 f) = schwartzToL2 (𝓕⁻ f) :=
  SchwartzMap.toLp_fourierInv_eq f

theorem coeFn_schwartzToL2 (f : 𝓢(V, ℂ)) :
    ((schwartzToL2 f : L2 V) : V → ℂ) =ᵐ[volume] (f : V → ℂ) :=
  SchwartzMap.coeFn_toLp (μ := (volume : Measure V)) f 2

/-- If two Schwartz functions are related by multiplication with the symbol, then the
multiplication operator maps the first to the second. -/
theorem mulOp_freeSymbol_schwartz (f g : 𝓢(V, ℂ)) (h : ∀ ξ, (freeSymbol ξ : ℂ) * f ξ = g ξ) :
    ∃ hmem : (schwartzToL2 f : L2 V) ∈ (mulOp (freeSymbol : V → ℝ)).domain,
      mulOp freeSymbol ⟨schwartzToL2 f, hmem⟩ = schwartzToL2 g := by
  have hae : (fun ξ => (freeSymbol ξ : ℂ) * ((schwartzToL2 f : L2 V) : V → ℂ) ξ)
      =ᵐ[volume] ((schwartzToL2 g : L2 V) : V → ℂ) := by
    filter_upwards [coeFn_schwartzToL2 f, coeFn_schwartzToL2 g] with ξ h1 h2
    rw [h1, h2, h ξ]
  have hmem : (schwartzToL2 f : L2 V) ∈ (mulOp (freeSymbol : V → ℝ)).domain :=
    (Lp.memLp (schwartzToL2 g)).ae_eq hae.symm
  exact ⟨hmem, mulOp_eq_of_ae _ ⟨schwartzToL2 f, hmem⟩ (schwartzToL2 g) hae.symm⟩

/-- Every Schwartz function lies in the domain of the multiplication operator by the symbol. -/
theorem schwartzToL2_mem_mulDomain (f : 𝓢(V, ℂ)) :
    (schwartzToL2 f : L2 V) ∈ (mulOp (freeSymbol : V → ℝ)).domain := by
  have hf : 𝓕 (𝓕⁻ f) = f := FourierTransform.fourier_fourierInv_eq f
  refine (mulOp_freeSymbol_schwartz f (𝓕 (negLaplacianSchwartz (𝓕⁻ f))) ?_).1
  intro ξ
  rw [negLaplacianSchwartz_apply, fourier_neg_laplacian, hf]

theorem dense_mulDomain_freeSymbol :
    Dense (((mulOp (freeSymbol : V → ℝ)).domain : Submodule ℂ (L2 V)) : Set (L2 V)) := by
  refine Dense.mono ?_ (dense_negLaplacianCore_domain (V := V))
  rintro x ⟨f, rfl⟩
  exact schwartzToL2_mem_mulDomain f

/-- **The maximal free Laplacian is self-adjoint.**  This is where Plancherel's theorem is used:
the Fourier transform is a unitary conjugating `-Δ` into a multiplication operator. -/
theorem freeLaplacian_isSelfAdjoint : IsSelfAdjoint (freeLaplacian : L2 V →ₗ.[ℂ] L2 V) :=
  conjPMap_isSelfAdjoint _ _
    (mulOp_isSelfAdjoint _ continuous_freeSymbol dense_mulDomain_freeSymbol)

theorem freeLaplacian_schwartz (f : 𝓢(V, ℂ)) :
    ∃ hmem : (schwartzToL2 f : L2 V) ∈ (freeLaplacian (V := V)).domain,
      freeLaplacian ⟨schwartzToL2 f, hmem⟩ = schwartzToL2 (negLaplacianSchwartz f) := by
  obtain ⟨hmem, hval⟩ := mulOp_freeSymbol_schwartz (𝓕 f) (𝓕 (negLaplacianSchwartz f))
    (fun ξ => by rw [negLaplacianSchwartz_apply, fourier_neg_laplacian])
  have hdom : (schwartzToL2 f : L2 V) ∈ (freeLaplacian (V := V)).domain := by
    show fourierU V (schwartzToL2 f) ∈ (mulOp (freeSymbol : V → ℝ)).domain
    rw [fourierU_schwartzToL2]
    exact hmem
  refine ⟨hdom, ?_⟩
  have h1 : freeLaplacian ⟨schwartzToL2 f, hdom⟩
      = (fourierU V).symm (mulOp freeSymbol ⟨fourierU V (schwartzToL2 f), hdom⟩) := rfl
  rw [h1]
  have h2 : (⟨fourierU V (schwartzToL2 f), hdom⟩ : (mulOp (freeSymbol : V → ℝ)).domain)
      = ⟨schwartzToL2 (𝓕 f), hmem⟩ := Subtype.ext (fourierU_schwartzToL2 f)
  rw [h2, hval, fourierU_symm_schwartzToL2]
  congr 1
  exact FourierTransform.fourierInv_fourier_eq _

/-- The maximal free Laplacian extends `-Δ` on Schwartz functions. -/
theorem negLaplacianCore_le_freeLaplacian :
    (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V) ≤ freeLaplacian := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨f, rfl⟩
    exact (freeLaplacian_schwartz f).1
  · rintro p q hpq
    obtain ⟨f, hf⟩ := p.2
    have hp : p = ⟨schwartzToL2 f, mem_negLaplacianCore_domain f⟩ := Subtype.ext hf.symm
    have hq : q = ⟨schwartzToL2 f, (freeLaplacian_schwartz f).1⟩ :=
      Subtype.ext (by rw [← hpq, ← hf])
    rw [hp, hq, negLaplacianCore_apply, (freeLaplacian_schwartz f).2]

/-- Every element of `L²` is an `L²`-limit of Schwartz functions. -/
theorem exists_schwartz_tendsto (h : L2 V) :
    ∃ psi : ℕ → 𝓢(V, ℂ), Tendsto (fun k => (schwartzToL2 (psi k) : L2 V)) atTop (𝓝 h) := by
  have hd := dense_negLaplacianCore_domain (V := V)
  have hmem : h ∈ closure (Set.range (fun f : 𝓢(V, ℂ) => (schwartzToL2 f : L2 V))) := by
    have hset : (((negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).domain : Submodule ℂ (L2 V)) : Set (L2 V))
        = Set.range (fun f : 𝓢(V, ℂ) => (schwartzToL2 f : L2 V)) := by
      ext x; simp [negLaplacianCore, LinearMap.mem_range]
    rw [← hset]
    exact hd h
  rw [mem_closure_iff_seq_limit] at hmem
  obtain ⟨x, hx, hxt⟩ := hmem
  choose psi hpsi using hx
  refine ⟨psi, ?_⟩
  simpa only [hpsi] using hxt

/-- A squeeze lemma for convergence in a normed space. -/
theorem tendsto_of_norm_sub_le {a b : ℕ → L2 V} {x y : L2 V}
    (h : ∀ k, ‖a k - x‖ ≤ ‖b k - y‖) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto a atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
  exact squeeze_zero (fun k => norm_nonneg _) h hb

/-- Schwartz functions are a core: every element of the domain of the maximal free Laplacian is
a limit, in the graph norm, of Schwartz functions. -/
theorem exists_schwartz_graph_approx (u : (freeLaplacian (V := V)).domain) :
    ∃ f : ℕ → 𝓢(V, ℂ),
      Tendsto (fun k => (schwartzToL2 (f k) : L2 V)) atTop (𝓝 (u : L2 V)) ∧
      Tendsto (fun k => (schwartzToL2 (negLaplacianSchwartz (f k)) : L2 V)) atTop
        (𝓝 (freeLaplacian u : L2 V)) := by
  have hu : fourierU V (u : L2 V) ∈ (mulOp (freeSymbol : V → ℝ)).domain := u.2
  set ghat : L2 V := fourierU V (u : L2 V) with hghat_def
  set W : L2 V := mulOp (freeSymbol : V → ℝ) ⟨ghat, hu⟩ with hW_def
  have hWae : ((W : L2 V) : V → ℂ) =ᵐ[volume] fun x => (freeSymbol x : ℂ) * ((ghat : L2 V) : V → ℂ) x :=
    coeFn_mulOp _ _
  have hLu : (freeLaplacian u : L2 V) = (fourierU V).symm W := conjPMap_apply _ _ u hu
  have husymm : ((fourierU V).symm ghat : L2 V) = (u : L2 V) := by
    rw [hghat_def, LinearIsometryEquiv.symm_apply_apply]
  obtain ⟨psi, hpsi⟩ := exists_schwartz_tendsto (ghat + W)
  have hrT : Function.HasTemperateGrowth (freeResolventSymbol : V → ℂ) :=
    hasTemperateGrowth_freeResolventSymbol
  set phi : ℕ → 𝓢(V, ℂ) := fun k => smulLeftCLM ℂ (freeResolventSymbol : V → ℂ) (psi k)
    with hphi_def
  have hphi_apply : ∀ k x, phi k x = freeResolventSymbol x * psi k x := by
    intro k x
    rw [hphi_def]
    simpa using smulLeftCLM_apply_apply hrT (psi k) x
  set chi : ℕ → 𝓢(V, ℂ) := fun k => 𝓕 (negLaplacianSchwartz (𝓕⁻ (phi k))) with hchi_def
  have hchi_apply : ∀ k x, chi k x = (freeSymbol x : ℂ) * phi k x := by
    intro k x
    rw [hchi_def]
    simp only [negLaplacianSchwartz_apply]
    rw [fourier_neg_laplacian, FourierTransform.fourier_fourierInv_eq]
  -- the two pointwise identities relating `ghat`, `W` and their sum
  have hkey1 : ∀ᵐ x ∂(volume : Measure V),
      freeResolventSymbol x * ((ghat + W : L2 V) : V → ℂ) x = ((ghat : L2 V) : V → ℂ) x := by
    filter_upwards [hWae, Lp.coeFn_add ghat W] with x h1 h2
    have hpos := one_add_freeSymbol_pos (V := V) x
    have hne : (1 + (freeSymbol x : ℂ)) ≠ 0 := by
      have : ((1 + freeSymbol x : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      push_cast at this
      exact this
    rw [h2]
    simp only [Pi.add_apply, h1, freeResolventSymbol]
    push_cast
    field_simp
  have hkey2 : ∀ᵐ x ∂(volume : Measure V),
      (freeSymbol x : ℂ) * freeResolventSymbol x * ((ghat + W : L2 V) : V → ℂ) x
        = ((W : L2 V) : V → ℂ) x := by
    filter_upwards [hkey1, hWae] with x h1 h2
    rw [mul_assoc, h1, h2]
  -- the two norm estimates
  have hest1 : ∀ k, ‖(schwartzToL2 (phi k) : L2 V) - ghat‖
      ≤ ‖(schwartzToL2 (psi k) : L2 V) - (ghat + W)‖ := by
    intro k
    have hb : ∀ᵐ x ∂(volume : Measure V), ‖(freeResolventSymbol x : ℂ)‖ ≤ 1 :=
      Filter.Eventually.of_forall (norm_freeResolventSymbol_le_one (V := V))
    have hae : (((schwartzToL2 (phi k) : L2 V) - ghat : L2 V) : V → ℂ)
        =ᵐ[volume] fun x => freeResolventSymbol x *
          (((schwartzToL2 (psi k) : L2 V) - (ghat + W) : L2 V) : V → ℂ) x := by
      filter_upwards [Lp.coeFn_sub (schwartzToL2 (phi k) : L2 V) ghat,
        Lp.coeFn_sub (schwartzToL2 (psi k) : L2 V) (ghat + W),
        coeFn_schwartzToL2 (phi k), coeFn_schwartzToL2 (psi k), hkey1] with x h1 h2 h3 h4 h5
      rw [h1, h2]
      simp only [Pi.sub_apply] at *
      rw [h3, h4, hphi_apply k x, mul_sub, h5]
    simpa using norm_le_of_ae_mul zero_le_one hb hae
  have hest2 : ∀ k, ‖(schwartzToL2 (chi k) : L2 V) - W‖
      ≤ ‖(schwartzToL2 (psi k) : L2 V) - (ghat + W)‖ := by
    intro k
    have hb : ∀ᵐ x ∂(volume : Measure V),
        ‖(freeSymbol x : ℂ) * freeResolventSymbol x‖ ≤ 1 :=
      Filter.Eventually.of_forall (norm_freeSymbol_mul_freeResolventSymbol_le_one (V := V))
    have hae : (((schwartzToL2 (chi k) : L2 V) - W : L2 V) : V → ℂ)
        =ᵐ[volume] fun x => ((freeSymbol x : ℂ) * freeResolventSymbol x) *
          (((schwartzToL2 (psi k) : L2 V) - (ghat + W) : L2 V) : V → ℂ) x := by
      filter_upwards [Lp.coeFn_sub (schwartzToL2 (chi k) : L2 V) W,
        Lp.coeFn_sub (schwartzToL2 (psi k) : L2 V) (ghat + W),
        coeFn_schwartzToL2 (chi k), coeFn_schwartzToL2 (psi k), hkey2] with x h1 h2 h3 h4 h5
      rw [h1, h2]
      simp only [Pi.sub_apply] at *
      rw [h3, h4, hchi_apply k x, hphi_apply k x, mul_sub, h5, mul_assoc]
    simpa using norm_le_of_ae_mul zero_le_one hb hae
  have hA : Tendsto (fun k => (schwartzToL2 (phi k) : L2 V)) atTop (𝓝 ghat) :=
    tendsto_of_norm_sub_le hest1 hpsi
  have hB : Tendsto (fun k => (schwartzToL2 (chi k) : L2 V)) atTop (𝓝 W) :=
    tendsto_of_norm_sub_le hest2 hpsi
  refine ⟨fun k => 𝓕⁻ (phi k), ?_, ?_⟩
  · have h := ((fourierU V).symm.continuous.tendsto ghat).comp hA
    rw [husymm] at h
    refine h.congr (fun k => ?_)
    simp only [Function.comp_apply]
    exact fourierU_symm_schwartzToL2 (phi k)
  · have h := ((fourierU V).symm.continuous.tendsto W).comp hB
    rw [← hLu] at h
    refine h.congr (fun k => ?_)
    have hne : 𝓕⁻ (chi k) = negLaplacianSchwartz (𝓕⁻ (phi k)) := by
      rw [hchi_def]
      exact FourierTransform.fourierInv_fourier_eq _
    simp only [Function.comp_apply]
    rw [fourierU_symm_schwartzToL2 (chi k), hne]

theorem negLaplacianCore_isClosable : (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).IsClosable :=
  (freeLaplacian_isSelfAdjoint.isClosed).isClosable.leIsClosable negLaplacianCore_le_freeLaplacian

/-- The closure of `-Δ` on Schwartz functions is the maximal free Laplacian. -/
theorem closure_negLaplacianCore :
    (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).closure = freeLaplacian := by
  refine le_antisymm ?_ ?_
  · rw [← le_graph_iff, ← negLaplacianCore_isClosable.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _ (le_graph_of_le negLaplacianCore_le_freeLaplacian)
      freeLaplacian_isSelfAdjoint.isClosed
  · refine le_of_le_graph ?_
    rw [← negLaplacianCore_isClosable.graph_closure_eq_closure_graph]
    rintro ⟨x, y⟩ hxy
    rw [LinearPMap.mem_graph_iff] at hxy
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨f, hf1, hf2⟩ := exists_schwartz_graph_approx u
    have hx : (u : L2 V) = x := hu.1
    have hy : freeLaplacian u = y := hu.2
    rw [hx] at hf1
    rw [hy] at hf2
    refine mem_closure_of_tendsto (hf1.prodMk_nhds hf2) (Filter.Eventually.of_forall ?_)
    intro k
    have := LinearPMap.mem_graph (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V)
      ⟨schwartzToL2 (f k), mem_negLaplacianCore_domain (f k)⟩
    rwa [negLaplacianCore_apply] at this

/-- **Essential self-adjointness of the free Laplacian.**

The Laplacian `-Δ`, defined on the core of Schwartz functions inside `L²(V; ℂ)`, is essentially
self-adjoint: its closure is a self-adjoint operator, and it has exactly one self-adjoint
extension (namely the operator `freeLaplacian` obtained from the Fourier multiplier `4π²‖ξ‖²`). -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel :
    IsSelfAdjoint (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V).closure ∧
      ∃! A : L2 V →ₗ.[ℂ] L2 V,
        IsSelfAdjoint A ∧ (negLaplacianCore : L2 V →ₗ.[ℂ] L2 V) ≤ A := by
  refine ⟨by rw [closure_negLaplacianCore]; exact freeLaplacian_isSelfAdjoint,
    ⟨freeLaplacian, ⟨freeLaplacian_isSelfAdjoint, negLaplacianCore_le_freeLaplacian⟩, ?_⟩⟩
  rintro B ⟨hB, hBle⟩
  have h1 : (freeLaplacian : L2 V →ₗ.[ℂ] L2 V) ≤ B := by
    rw [← closure_negLaplacianCore]
    rw [← le_graph_iff, ← negLaplacianCore_isClosable.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _ (le_graph_of_le hBle) hB.isClosed
  have h2 : B ≤ (freeLaplacian : L2 V →ₗ.[ℂ] L2 V) := by
    have := adjoint_le_adjoint (freeLaplacian_isSelfAdjoint.dense_domain) h1
    rwa [LinearPMap.isSelfAdjoint_def.mp hB, LinearPMap.isSelfAdjoint_def.mp
      freeLaplacian_isSelfAdjoint] at this
  exact le_antisymm h2 h1

end

end Brockian

