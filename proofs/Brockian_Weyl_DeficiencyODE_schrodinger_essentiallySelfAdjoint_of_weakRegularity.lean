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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter

namespace Brockian.Weyl.DeficiencyODE

/-!
## Abstract deficiency criterion

An unbounded operator is presented here as a linear map `T` on a complex Hilbert space `H`
together with a distinguished (dense) *domain* `D`; the operator of interest is the
restriction `T|_D`.  Essential self-adjointness of a densely defined symmetric operator is
equivalent to the vanishing of both deficiency spaces `ker (T* ∓ i)`, i.e. to the density of
the ranges of `T ± i`; this is the definition used below.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `T` is symmetric on the domain `D`: `⟪T x, y⟫ = ⟪x, T y⟫` for `x, y ∈ D`. -/
def IsSymmetricOn (D : Submodule ℂ H) (T : H →ₗ[ℂ] H) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

/-- The basic (deficiency-index) criterion for essential self-adjointness of a densely
defined symmetric operator: the ranges of `T ± i` on the domain `D` are dense, equivalently
both deficiency spaces are trivial. -/
def EssentiallySelfAdjointOn (D : Submodule ℂ H) (T : H →ₗ[ℂ] H) : Prop :=
  Dense ((D.map (T + Complex.I • LinearMap.id) : Submodule ℂ H) : Set H) ∧
    Dense ((D.map (T - Complex.I • LinearMap.id) : Submodule ℂ H) : Set H)

/-- If `T` is a (globally defined) symmetric operator and `z` is non-real, then the range of
`T + z` over any dense domain is dense: there are no deficiency vectors at `z`. -/
theorem dense_map_add_smul_of_symmetric [CompleteSpace H] (T : H →ₗ[ℂ] H)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (z : ℂ) (hz : z.im ≠ 0) :
    Dense ((D.map (T + z • LinearMap.id) : Submodule ℂ H) : Set H) := by
  set A : H →ₗ[ℂ] H := T + z • LinearMap.id with hA
  have horth : (D.map A)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    -- a vector orthogonal to the range of `T + z` is a deficiency vector: `T y = -conj z • y`
    have key : ∀ x ∈ D, ⟪x, T y + (conj z) • y⟫_ℂ = 0 := by
      intro x hx
      have h0 := hy (A x) ⟨x, hx, rfl⟩
      rw [hA] at h0
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        inner_add_left, inner_smul_left] at h0
      rw [hT x y] at h0
      rw [inner_add_right, inner_smul_right]
      linear_combination h0
    have hu : T y + (conj z) • y = 0 :=
      hD.eq_zero_of_inner_right fun v => key v v.2
    have hTy : T y = -((conj z) • y) := by linear_combination (norm := module) hu
    -- symmetry forces the eigenvalue to be real, which is impossible unless `y = 0`
    have h1 : ⟪y, T y⟫_ℂ = ⟪T y, y⟫_ℂ := (hT y y).symm
    rw [hTy] at h1
    simp only [inner_neg_right, inner_neg_left, inner_smul_right, inner_smul_left,
      RingHomCompTriple.comp_apply, RingHom.id_apply] at h1
    have h2 : (z - conj z) * ⟪y, y⟫_ℂ = 0 := by linear_combination h1
    have h3 : z - conj z ≠ 0 := by
      rw [Complex.sub_conj]
      simp [hz, Complex.ext_iff]
    have h4 : ⟪y, y⟫_ℂ = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h h3
      · exact h
    exact inner_self_eq_zero.mp h4
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  exact horth

/-- **Essential self-adjointness criterion.** A symmetric operator that is defined on all of
`H` is essentially self-adjoint on every dense domain. -/
theorem essentiallySelfAdjointOn_of_symmetric [CompleteSpace H] (T : H →ₗ[ℂ] H)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (D : Submodule ℂ H) (hD : Dense (D : Set H)) :
    EssentiallySelfAdjointOn D T := by
  refine ⟨dense_map_add_smul_of_symmetric T hT D hD Complex.I (by simp), ?_⟩
  have h : T - Complex.I • LinearMap.id
      = T + (-Complex.I) • (LinearMap.id : H →ₗ[ℂ] H) := by
    rw [neg_smul, ← sub_eq_add_neg]
  rw [h]
  exact dense_map_add_smul_of_symmetric T hT D hD (-Complex.I) (by simp)

end Abstract

/-!
## The Schrödinger operator on `ℓ²(ℤ)`

`(Hψ) n = ψ (n + 1) + ψ (n - 1) + V n * ψ n`, the second-order difference (Weyl) operator
with potential `V`.
-/

/-- The Hilbert space `ℓ²(ℤ)`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

lemma memℓp_comp_addRight {f : ℤ → ℂ} (hf : Memℓp f 2) (k : ℤ) :
    Memℓp (fun n => f (n + k)) 2 := by
  have h2 : (0:ℝ) < (2:ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff h2] at hf ⊢
  exact (Equiv.addRight k).summable_iff.mpr hf

lemma memℓp_mul_bounded {V : ℤ → ℝ} {C : ℝ} (hV : ∀ n, |V n| ≤ C) {f : ℤ → ℂ}
    (hf : Memℓp f 2) : Memℓp (fun n => (V n : ℂ) * f n) 2 := by
  have h2 : (0:ℝ) < (2:ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff h2] at hf ⊢
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hV 0)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hf.mul_left (C ^ (2:ℝ≥0∞).toReal))
  have h : ‖(V n : ℂ) * f n‖ = |V n| * ‖f n‖ := by simp [Complex.norm_real]
  rw [h, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  gcongr
  exact hV n

/-- The shift `(S_k ψ) n = ψ (n + k)` on `ℓ²(ℤ)`. -/
noncomputable def shiftLM (k : ℤ) : L2Z →ₗ[ℂ] L2Z where
  toFun ψ := ⟨fun n => ψ (n + k), memℓp_comp_addRight (lp.memℓp ψ) k⟩
  map_add' := by intro f g; ext n; simp
  map_smul' := by intro c f; ext n; simp

/-- Multiplication by a bounded real potential on `ℓ²(ℤ)`. -/
noncomputable def potentialLM (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) : L2Z →ₗ[ℂ] L2Z where
  toFun ψ := ⟨fun n => (V n : ℂ) * ψ n, memℓp_mul_bounded hV.choose_spec (lp.memℓp ψ)⟩
  map_add' := by intro f g; ext n; simp [mul_add]
  map_smul' := by intro c f; ext n; simp; ring

/-- The Schrödinger operator `(Hψ) n = ψ (n+1) + ψ (n-1) + V n * ψ n` on `ℓ²(ℤ)`. -/
noncomputable def schrodingerLM (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) : L2Z →ₗ[ℂ] L2Z :=
  shiftLM 1 + shiftLM (-1) + potentialLM V hV

lemma schrodingerLM_apply (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) (ψ : L2Z) (n : ℤ) :
    (schrodingerLM V hV ψ) n = ψ (n + 1) + ψ (n - 1) + (V n : ℂ) * ψ n := by
  show ψ (n + 1) + ψ (n + (-1)) + (V n : ℂ) * ψ n = _
  rw [← sub_eq_add_neg]

/-- The domain: sequences with finite support, i.e. the span of the standard basis vectors. -/
noncomputable def finSupp : Submodule ℂ L2Z :=
  Submodule.span ℂ (Set.range fun n : ℤ => (lp.single 2 n (1 : ℂ) : L2Z))

lemma dense_finSupp : Dense ((finSupp : Submodule ℂ L2Z) : Set L2Z) := by
  intro f
  have hs : HasSum (fun i : ℤ => (lp.single 2 i (f i) : L2Z)) f := lp.hasSum_single (by simp) f
  refine mem_closure_of_tendsto hs (Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun i _ => ?_
  have h : (lp.single 2 i (f i) : L2Z) = (f i) • (lp.single 2 i (1 : ℂ) : L2Z) := by
    rw [← lp.single_smul]
    simp
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma inner_shiftLM_left (k : ℤ) (φ ψ : L2Z) :
    ⟪shiftLM k φ, ψ⟫_ℂ = ⟪φ, shiftLM (-k) ψ⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← (Equiv.subRight k).tsum_eq (fun n : ℤ => ⟪(shiftLM k φ) n, ψ n⟫_ℂ)]
  refine tsum_congr fun m => ?_
  show ⟪φ ((m - k) + k), ψ (m - k)⟫_ℂ = ⟪φ m, ψ (m + -k)⟫_ℂ
  simp [sub_eq_add_neg]

lemma inner_potentialLM_left (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) (φ ψ : L2Z) :
    ⟪potentialLM V hV φ, ψ⟫_ℂ = ⟪φ, potentialLM V hV ψ⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  show ⟪(V n : ℂ) * φ n, ψ n⟫_ℂ = ⟪φ n, (V n : ℂ) * ψ n⟫_ℂ
  simp [RCLike.inner_apply, mul_assoc, mul_left_comm]

/-- The Schrödinger operator is symmetric on all of `ℓ²(ℤ)`. -/
lemma schrodingerLM_symmetric (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) (φ ψ : L2Z) :
    ⟪schrodingerLM V hV φ, ψ⟫_ℂ = ⟪φ, schrodingerLM V hV ψ⟫_ℂ := by
  show ⟪shiftLM 1 φ + shiftLM (-1) φ + potentialLM V hV φ, ψ⟫_ℂ
      = ⟪φ, shiftLM 1 ψ + shiftLM (-1) ψ + potentialLM V hV ψ⟫_ℂ
  rw [inner_add_left, inner_add_left, inner_add_right, inner_add_right,
    inner_shiftLM_left 1, inner_shiftLM_left (-1), inner_potentialLM_left]
  simp only [neg_neg]
  ring

/-- **Essential self-adjointness of the Schrödinger operator under weak regularity of the
potential.**

The potential `V` is assumed only to be real valued and bounded; no continuity, smoothness or
any other regularity is required (weak regularity).  The Schrödinger operator
`(Hψ) n = ψ (n+1) + ψ (n-1) + V n * ψ n` on `ℓ²(ℤ)`, defined on the domain `finSupp` of
finitely supported sequences, is then symmetric and essentially self-adjoint: both deficiency
spaces vanish, i.e. the ranges of `H ± i` on the domain are dense.  This is the unconditional
form of the statement: no essential self-adjointness (limit-point) hypothesis is assumed. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity
    (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) :
    IsSymmetricOn finSupp (schrodingerLM V hV) ∧
      EssentiallySelfAdjointOn finSupp (schrodingerLM V hV) :=
  ⟨fun x _ y _ => schrodingerLM_symmetric V hV x y,
    essentiallySelfAdjointOn_of_symmetric _ (schrodingerLM_symmetric V hV) _ dense_finSupp⟩

end Brockian.Weyl.DeficiencyODE

