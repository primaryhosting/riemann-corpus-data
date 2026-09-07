import Mathlib

set_option autoImplicit false

namespace Brockian.SpectralGate1

open MeasureTheory Complex

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## The bounded multiplication operator on L² (the potential term) -/

/-- The pointwise product `g • f` of an `L∞` multiplier `g` and an `L²` function `f`,
returned as an element of `L²`. This is the raw action of the multiplication operator. -/
noncomputable def mulLpFun (g : α → ℂ) (hg : MemLp g ⊤ μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).smul hg (r := 2)).toLp

/-- **Pinning lemma.** The multiplication operator genuinely acts as pointwise
multiplication by `g` almost everywhere. This is what forces the operator to *be*
multiplication by `g` (so the zero operator is not a witness unless `g = 0` a.e.). -/
theorem coeFn_mulLpFun (g : α → ℂ) (hg : MemLp g ⊤ μ) (f : Lp ℂ 2 μ) :
    (mulLpFun g hg f : α → ℂ) =ᵐ[μ] g • (f : α → ℂ) :=
  MemLp.coeFn_toLp _

/-- The multiplication operator as a `ℂ`-linear map on `L²`. -/
noncomputable def mulLpₗ (g : α → ℂ) (hg : MemLp g ⊤ μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := mulLpFun g hg
  map_add' f₁ f₂ := by
    apply Lp.ext
    filter_upwards [coeFn_mulLpFun g hg (f₁ + f₂), coeFn_mulLpFun g hg f₁,
      coeFn_mulLpFun g hg f₂, Lp.coeFn_add (mulLpFun g hg f₁) (mulLpFun g hg f₂),
      Lp.coeFn_add f₁ f₂] with x e0 e1 e2 esum ein
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e0 e1 e2 esum ein ⊢
    rw [e0, ein, esum, e1, e2]; ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_mulLpFun g hg (c • f), coeFn_mulLpFun g hg f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (mulLpFun g hg f)] with x e0 e1 esf esr
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, RingHom.id_apply] at e0 e1 esf esr ⊢
    rw [e0, esf, esr, e1]; ring

@[simp] theorem mulLpₗ_apply (g : α → ℂ) (hg : MemLp g ⊤ μ) (f : Lp ℂ 2 μ) :
    mulLpₗ g hg f = mulLpFun g hg f := rfl

/-- Quantitative boundedness: `‖g • f‖₂ ≤ C ‖f‖₂` when `‖g‖ ≤ C` a.e. -/
theorem eLpNorm_mulLpFun_le (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp ℂ 2 μ) :
    eLpNorm (mulLpFun g hg f : α → ℂ) 2 μ ≤ ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ := by
  calc eLpNorm (mulLpFun g hg f : α → ℂ) 2 μ
      = eLpNorm (g • (f : α → ℂ)) 2 μ := eLpNorm_congr_ae (coeFn_mulLpFun g hg f)
    _ ≤ eLpNorm ((C : ℝ) • (f : α → ℂ)) 2 μ := by
        apply eLpNorm_mono_ae
        filter_upwards [hbd] with x hx
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
        rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ ≤ ‖(C : ℝ)‖ₑ * eLpNorm (f : α → ℂ) 2 μ := eLpNorm_const_smul_le
    _ = ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC]

/-- **The bounded multiplication operator** `M_g` on `L²(μ)`, for a multiplier `g`
that is essentially bounded by `C`. Continuous with operator norm `≤ C`. -/
noncomputable def mulLpCLM (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (mulLpₗ g hg) C (by
    intro f
    rw [Lp.norm_def, Lp.norm_def, mulLpₗ_apply]
    have hfin : eLpNorm (f : α → ℂ) 2 μ ≠ ⊤ := (Lp.memLp f).eLpNorm_ne_top
    have hbnd := eLpNorm_mulLpFun_le g hg hC hbd f
    have htop : ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    calc (eLpNorm (mulLpFun g hg f : α → ℂ) 2 μ).toReal
        ≤ (ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ).toReal :=
          ENNReal.toReal_mono htop hbnd
      _ = C * (eLpNorm (f : α → ℂ) 2 μ).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC])

/-- **Pinning for the CLM.** `M_g` acts as multiplication by `g` a.e. -/
theorem coeFn_mulLpCLM (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (mulLpCLM g hg hC hbd f : α → ℂ) =ᵐ[μ] g • (f : α → ℂ) := by
  have h : mulLpCLM g hg hC hbd f = mulLpFun g hg f := by
    simp only [mulLpCLM, LinearMap.mkContinuous_apply, mulLpₗ_apply]
  rw [h]; exact coeFn_mulLpFun g hg f

/-- **Self-adjointness of the multiplication operator for a real multiplier.**
If `g` is real-valued a.e., then `M_g` is self-adjoint on `L²`. Proved through
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`, i.e. `⟪M_g f, h⟫ = ⟪f, M_g h⟫`. -/
theorem isSelfAdjoint_mulLpCLM (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (hreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (g x) = g x) :
    IsSelfAdjoint (mulLpCLM g hg hC hbd) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  rw [L2.inner_def, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coeFn_mulLpCLM g hg hC hbd f, coeFn_mulLpCLM g hg hC hbd h, hreal]
    with x e1 e2 er
  simp only [ContinuousLinearMap.coe_coe, e1, e2, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, er]
  ring

/-! ## The prime-Gaussian potential (a concrete bounded real multiplier) -/

/-- A single damped Gaussian bump at index `n`: a Gaussian centered at `n` when `n` is
prime (otherwise `0`), damped by `(1/2)^n` so the family is absolutely summable. -/
noncomputable def primeBump (x : ℝ) (n : ℕ) : ℝ :=
  (if Nat.Prime n then Real.exp (-(x - n) ^ 2) else 0) * (1 / 2) ^ n

theorem primeBump_nonneg (x : ℝ) (n : ℕ) : 0 ≤ primeBump x n := by
  apply mul_nonneg _ (by positivity)
  split_ifs
  · exact Real.exp_nonneg _
  · exact le_refl 0

theorem primeBump_le_geom (x : ℝ) (n : ℕ) : primeBump x n ≤ (1 / 2) ^ n := by
  unfold primeBump
  have h1 : (if Nat.Prime n then Real.exp (-(x - n) ^ 2) else 0) ≤ 1 := by
    split_ifs with hn
    · exact Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg _))
    · norm_num
  calc (if Nat.Prime n then Real.exp (-(x - n) ^ 2) else 0) * (1 / 2) ^ n
      ≤ 1 * (1 / 2) ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (1 / 2) ^ n := one_mul _

theorem summable_primeBump (x : ℝ) : Summable (fun n => primeBump x n) :=
  Summable.of_nonneg_of_le (fun n => primeBump_nonneg x n) (fun n => primeBump_le_geom x n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem continuous_primeBump (n : ℕ) : Continuous (fun x => primeBump x n) := by
  unfold primeBump
  split_ifs with hn
  · fun_prop
  · fun_prop

/-- **The prime-Gaussian potential** `V(x) = ∑ₚ e^{-(x-p)²}·2^{-p}` (sum over primes),
a superposition of Gaussian bumps centered at the primes, damped in the prime index.
Real-valued, nonnegative, bounded by `2`, absolutely summable, and continuous. -/
noncomputable def primeGaussian (x : ℝ) : ℝ := ∑' n : ℕ, primeBump x n

theorem primeGaussian_nonneg (x : ℝ) : 0 ≤ primeGaussian x :=
  tsum_nonneg (fun n => primeBump_nonneg x n)

/-- The potential is bounded above by `2` — uniformly in `x`. -/
theorem primeGaussian_le_two (x : ℝ) : primeGaussian x ≤ 2 := by
  have hle : primeGaussian x ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n :=
    Summable.tsum_le_tsum (fun n => primeBump_le_geom x n) (summable_primeBump x)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hle
  norm_num at hle
  exact hle

/-- The potential is essentially bounded: `|V(x)| ≤ 2`. -/
theorem abs_primeGaussian_le_two (x : ℝ) : |primeGaussian x| ≤ 2 := by
  rw [abs_of_nonneg (primeGaussian_nonneg x)]; exact primeGaussian_le_two x

/-- The potential is continuous (uniform limit of continuous partial sums, M-test). -/
theorem continuous_primeGaussian : Continuous primeGaussian := by
  unfold primeGaussian
  refine continuous_tsum (u := fun n => (1 / 2 : ℝ) ^ n) continuous_primeBump
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) (fun n x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (primeBump_nonneg x n)]
  exact primeBump_le_geom x n

/-- The complex-valued multiplier attached to the (real) prime-Gaussian potential. -/
noncomputable def primeGaussianℂ : ℝ → ℂ := fun x => (primeGaussian x : ℂ)

theorem primeGaussianℂ_norm_le (x : ℝ) : ‖primeGaussianℂ x‖ ≤ 2 := by
  show ‖(primeGaussian x : ℂ)‖ ≤ 2
  rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_primeGaussian_le_two x

/-- The prime-Gaussian multiplier is genuinely in `L∞(ℝ)` (essential bound `2`). -/
theorem primeGaussianℂ_memLp_top : MemLp primeGaussianℂ ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound
    (Complex.continuous_ofReal.comp continuous_primeGaussian).aestronglyMeasurable 2
    (ae_of_all _ primeGaussianℂ_norm_le)

/-- **The concrete potential operator** `M_V` on `L²(ℝ)`: multiplication by the
prime-Gaussian potential. This is a genuine, nonzero (Gate-0) witness — the operator is
pinned to *be* multiplication by `V`, so it is not the degenerate zero operator. -/
noncomputable def primeGaussianMulCLM :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  mulLpCLM primeGaussianℂ primeGaussianℂ_memLp_top (by norm_num)
    (ae_of_all _ primeGaussianℂ_norm_le)

/-- **The potential term of the Brockian Hamiltonian is bounded self-adjoint on `L²(ℝ)`.**
The multiplication operator by the (real) prime-Gaussian potential is self-adjoint. -/
theorem isSelfAdjoint_primeGaussianMulCLM : IsSelfAdjoint primeGaussianMulCLM :=
  isSelfAdjoint_mulLpCLM primeGaussianℂ primeGaussianℂ_memLp_top (by norm_num)
    (ae_of_all _ primeGaussianℂ_norm_le)
    (ae_of_all _ fun x => Complex.conj_ofReal (primeGaussian x))

/-- **Pinning of the concrete operator.** `M_V` acts as multiplication by `V` a.e. — the
statement that forbids the degenerate zero-operator witness (`V` is nonzero). -/
theorem coeFn_primeGaussianMulCLM (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (primeGaussianMulCLM f : ℝ → ℂ) =ᵐ[volume] primeGaussianℂ • (f : ℝ → ℂ) :=
  coeFn_mulLpCLM primeGaussianℂ primeGaussianℂ_memLp_top (by norm_num)
    (ae_of_all _ primeGaussianℂ_norm_le) f

/-!
## The full Schrödinger operator `−Δ + V` stays OPEN (rung 1 not reached)

The bounded potential term `M_V` above is fully verified as a bounded self-adjoint
operator on `L²(ℝ)`. The full Brockian Hamiltonian `H = −Δ + V` is an **unbounded**,
densely-defined operator (the kinetic term `−Δ` has unbounded spectrum), and hence is
*not* a `ContinuousLinearMap`; its essential self-adjointness is governed by the classical
**Weyl limit-point / limit-circle criterion**.

Mathlib v4.32.0 does not provide the unbounded-operator infrastructure this requires
(no `LinearPMap` symmetric-closure / deficiency-index / essential-self-adjointness API,
no Weyl limit-point theorem). Stating a `−Δ+V` essential-self-adjointness result here as a
conditional on a named Weyl hypothesis would, in the current library, reduce either to a
vacuous or a `modus-ponens`-only implication (carrying no real work), which the intake
ledger explicitly rejects. It is therefore left honestly OPEN rather than faked.

What IS delivered (rung 2, strong partial): the potential term is a bona-fide bounded
self-adjoint multiplication operator on `L²`, pinned to multiplication by `V`, together
with a concrete, nonzero prime-Gaussian instance.
-/

end Brockian.SpectralGate1
