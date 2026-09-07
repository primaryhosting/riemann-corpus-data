/-
  Brockian/WeylMulReal.lean — essential self-adjointness of multiplication by a
  real essentially-bounded function on L² (the free/potential model rung
  complementary to FreeLaplacian).

  ## What is proved

  1. **Real L∞ multiplication is ESA.** For real-valued essentially-bounded `g`,
     `mulLpCLM g` is self-adjoint (reused from `SpectralGate1`) and therefore
     essentially self-adjoint via `ESA.clm_essentiallySelfAdjoint`.

  2. **Concrete instances.** Constant real multipliers (including the identity
     multiplier `1`) and the prime-Gaussian potential multiplier are ESA.

  3. **Sum of two real multiplication operators** is bounded self-adjoint, hence ESA.

  4. **Abstract free-multiplication model** `FreeMulModel`: a real L∞ multiplier
     packaged with its CLM and ESA theorem (dual to `FreeLaplacianModel`).

  ## What is NOT proved

  * Unbounded multiplication by `ξ ↦ ξ²` (or `x ↦ x²`) on `L²(ℝ)` as a
    densely-defined `LinearPMap`. That would need an unbounded-operator domain
    (e.g. weighted Sobolev / maximal multiplication domain) and is left honestly
    OPEN — no fake unbounded construction is claimed here.

  Verification (spec §2A): AXLE @ lean-4.32.0;
  axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.SpectralGate1
import Brockian.WeylEssSelfAdjoint
import Brockian.WeylOperator

open MeasureTheory Complex
open scoped InnerProductSpace ComplexConjugate
open Brockian.SpectralGate1
open Brockian.Weyl.Operator Brockian.Weyl.ESA

namespace Brockian.Weyl.MulReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Real L∞ multiplication ⇒ ESA -/

/-- **Essential self-adjointness of a real L∞ multiplier.** If `g` is essentially
bounded by `C` and real-valued a.e., then `M_g = mulLpCLM g` (viewed as a
full-domain `LinearPMap`) is essentially self-adjoint. -/
theorem mulLpCLM_essentiallySelfAdjoint (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ}
    (hC : 0 ≤ C) (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (hreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (g x) = g x) :
    EssentiallySelfAdjoint ((mulLpCLM g hg hC hbd).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ (isSelfAdjoint_mulLpCLM g hg hC hbd hreal)

/-! ### Concrete instances: constant / identity / prime-Gaussian -/

/-- Constant complex function with value `c`. -/
noncomputable def constFun (c : ℂ) : α → ℂ := fun _ => c

/-- Constants are in `L∞` on any measure space (no topology on `α` required). -/
theorem constFun_memLp_top (c : ℂ) : MemLp (constFun (α := α) c) ⊤ μ :=
  memLp_top_of_bound aestronglyMeasurable_const ‖c‖
    (ae_of_all _ fun _ => le_rfl)

theorem constFun_norm_le (c : ℂ) : ∀ᵐ x ∂μ, ‖constFun (α := α) c x‖ ≤ ‖c‖ :=
  ae_of_all _ fun _ => le_rfl

theorem constFun_real (c : ℝ) :
    ∀ᵐ x ∂μ, (starRingEnd ℂ) (constFun (α := α) (c : ℂ) x) = constFun (α := α) (c : ℂ) x :=
  ae_of_all _ fun _ => Complex.conj_ofReal c

/-- **Multiplication by a real constant** as a bounded operator on `L²(μ)`. -/
noncomputable def constMulCLM (c : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  mulLpCLM (constFun (c : ℂ)) (constFun_memLp_top (c : ℂ)) (norm_nonneg (c : ℂ))
    (constFun_norm_le (c : ℂ))

theorem isSelfAdjoint_constMulCLM (c : ℝ) : IsSelfAdjoint (constMulCLM (μ := μ) c) :=
  isSelfAdjoint_mulLpCLM _ _ _ _ (constFun_real c)

/-- **Constant real multiplier is essentially self-adjoint.** -/
theorem constMul_essentiallySelfAdjoint (c : ℝ) :
    EssentiallySelfAdjoint ((constMulCLM (μ := μ) c).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ (isSelfAdjoint_constMulCLM c)

/-- Identity multiplier: multiplication by the constant `1`. -/
noncomputable def oneMulCLM : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  constMulCLM (1 : ℝ)

theorem isSelfAdjoint_oneMulCLM : IsSelfAdjoint (oneMulCLM (μ := μ)) :=
  isSelfAdjoint_constMulCLM 1

/-- **Identity multiplier is essentially self-adjoint.** -/
theorem oneMul_essentiallySelfAdjoint :
    EssentiallySelfAdjoint ((oneMulCLM (μ := μ)).toPMap ⊤) :=
  constMul_essentiallySelfAdjoint 1

/-- L² space of the Brockian potential (notation). -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **Prime-Gaussian potential multiplier is essentially self-adjoint** (concrete
Gate-1 potential instance, packaged here for the free/potential model rung). -/
theorem primeGaussianMul_essentiallySelfAdjoint :
    EssentiallySelfAdjoint (primeGaussianMulCLM.toPMap ⊤) :=
  clm_essentiallySelfAdjoint primeGaussianMulCLM isSelfAdjoint_primeGaussianMulCLM

/-! ### Sum of two real multiplication operators -/

/-- **Sum of two real L∞ multipliers is self-adjoint.** Each summand is SA, so the
sum is SA by `IsSelfAdjoint.add`. -/
theorem add_mulLpCLM_isSelfAdjoint (g h : α → ℂ) (hg : MemLp g ⊤ μ) (hh : MemLp h ⊤ μ)
    {Cg Ch : ℝ} (hCg : 0 ≤ Cg) (hCh : 0 ≤ Ch)
    (hgbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ Cg) (hhbd : ∀ᵐ x ∂μ, ‖h x‖ ≤ Ch)
    (hgreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (g x) = g x)
    (hhreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (h x) = h x) :
    IsSelfAdjoint (mulLpCLM g hg hCg hgbd + mulLpCLM h hh hCh hhbd) :=
  (isSelfAdjoint_mulLpCLM g hg hCg hgbd hgreal).add
    (isSelfAdjoint_mulLpCLM h hh hCh hhbd hhreal)

/-- **Sum of two real L∞ multipliers is essentially self-adjoint.** -/
theorem add_mulLpCLM_essentiallySelfAdjoint (g h : α → ℂ)
    (hg : MemLp g ⊤ μ) (hh : MemLp h ⊤ μ) {Cg Ch : ℝ} (hCg : 0 ≤ Cg) (hCh : 0 ≤ Ch)
    (hgbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ Cg) (hhbd : ∀ᵐ x ∂μ, ‖h x‖ ≤ Ch)
    (hgreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (g x) = g x)
    (hhreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (h x) = h x) :
    EssentiallySelfAdjoint
      ((mulLpCLM g hg hCg hgbd + mulLpCLM h hh hCh hhbd).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _
    (add_mulLpCLM_isSelfAdjoint g h hg hh hCg hCh hgbd hhbd hgreal hhreal)

/-- Sum of two constant real multipliers is ESA (concrete special case). -/
theorem add_constMul_essentiallySelfAdjoint (c d : ℝ) :
    EssentiallySelfAdjoint
      ((constMulCLM (μ := μ) c + constMulCLM (μ := μ) d).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _
    ((isSelfAdjoint_constMulCLM c).add (isSelfAdjoint_constMulCLM d))

/-- Bounded free/kinetic CLM + real L∞ multiplier remains ESA. -/
theorem add_clm_mul_essentiallySelfAdjoint {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hT : IsSelfAdjoint T) (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (hreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (g x) = g x) :
    EssentiallySelfAdjoint ((T + mulLpCLM g hg hC hbd).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _
    (hT.add (isSelfAdjoint_mulLpCLM g hg hC hbd hreal))

/-! ### Abstract free-multiplication model (real L∞ on Lp) -/

/-- **Free/potential multiplication model.** A real essentially-bounded multiplier
on `L²(μ)`, dual to `FreeLaplacianModel` (Fourier kinetic side). Inhabiting with a
genuine unbounded `ξ²` multiplication is the remaining Mathlib-scale step. -/
structure FreeMulModel (α : Type*) [MeasurableSpace α] (μ : Measure α) where
  g : α → ℂ
  hg : MemLp g ⊤ μ
  C : ℝ
  hC : 0 ≤ C
  hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C
  hreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (g x) = g x

/-- The bounded multiplication operator of a free-multiplication model. -/
noncomputable def FreeMulModel.mulOp (M : FreeMulModel α μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  mulLpCLM M.g M.hg M.hC M.hbd

theorem FreeMulModel.isSelfAdjoint_mulOp (M : FreeMulModel α μ) :
    IsSelfAdjoint M.mulOp :=
  isSelfAdjoint_mulLpCLM M.g M.hg M.hC M.hbd M.hreal

/-- **ESA of a free-multiplication model.** -/
theorem FreeMulModel.essentiallySelfAdjoint_mulOp (M : FreeMulModel α μ) :
    EssentiallySelfAdjoint (M.mulOp.toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ M.isSelfAdjoint_mulOp

/-- Concrete inhabitant: constant real multiplier. -/
noncomputable def constFreeMulModel (c : ℝ) : FreeMulModel α μ where
  g := constFun (c : ℂ)
  hg := constFun_memLp_top (c : ℂ)
  C := ‖(c : ℂ)‖
  hC := norm_nonneg _
  hbd := constFun_norm_le (c : ℂ)
  hreal := constFun_real c

/-- Concrete inhabitant: prime-Gaussian potential on `L²(ℝ)`. -/
noncomputable def primeGaussianFreeMulModel : FreeMulModel ℝ volume where
  g := primeGaussianℂ
  hg := primeGaussianℂ_memLp_top
  C := 2
  hC := by norm_num
  hbd := ae_of_all _ primeGaussianℂ_norm_le
  hreal := ae_of_all _ fun x => Complex.conj_ofReal (primeGaussian x)

/-- Identity free-multiplication model (constant `1`). -/
noncomputable def oneFreeMulModel : FreeMulModel α μ :=
  constFreeMulModel 1

theorem constFreeMulModel_essentiallySelfAdjoint (c : ℝ) :
    EssentiallySelfAdjoint ((constFreeMulModel (α := α) (μ := μ) c).mulOp.toPMap ⊤) :=
  (constFreeMulModel (α := α) (μ := μ) c).essentiallySelfAdjoint_mulOp

theorem primeGaussianFreeMulModel_essentiallySelfAdjoint :
    EssentiallySelfAdjoint (primeGaussianFreeMulModel.mulOp.toPMap ⊤) :=
  primeGaussianFreeMulModel.essentiallySelfAdjoint_mulOp

/-!
## Honest OPEN note — unbounded multiplication by `x²` / `ξ²`

The constructions above are **bounded** (essentially bounded multipliers → CLMs).
Genuine multiplication by the unbounded symbol `x ↦ x²` on a dense domain in
`L²(ℝ)` (or `ξ ↦ ξ²` in Fourier space without cutoffs) is **not** claimed here:
that requires an unbounded `LinearPMap` domain and is complementary open work to
the free Laplacian in `WeylFreeLaplacian` / `WeylFreeLaplacian2`. Discrete/bounded
`ξ²` models live in `WeylFreeLaplacian2.multCLM` / `sqMultCLM`.
-/

end Brockian.Weyl.MulReal
