import Brockian.Fin5
import Brockian.Defs
import Brockian.Rayleigh
import Brockian.Gap
import Brockian.Poincare
import Brockian.LowerBound
import Brockian.LtOne
import Brockian.Perturb
import Brockian.LimitMatrices
import Brockian.FamilyDefs
import Brockian.LimitA
import Brockian.LimitB
import Brockian.GapLimits
import Brockian.Range
import Brockian.Spectrum
import Brockian.OpNorm
import Brockian.MinMax
import Brockian.UnbalancedPentagonLimits

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

import Brockian.LimitA
import Brockian.LimitB
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator-norm form of the two matrix limits

The entrywise `ℓ¹` norm `nrm1` dominates the `ℓ²` operator norm of a `5 × 5` real matrix
(`opNorm_le_nrm1`).  Consequently the entrywise convergences `Qa_tendsto_Qmin` and
`Qb_tendsto_Qmax` upgrade to convergence in the operator norm.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Finset Filter Topology
open scoped Matrix.Norms.L2Operator

/-- `√(∑ |wᵢ|²) ≤ ∑ |wᵢ|`. -/
lemma sqrt_sum_sq_le_sum_abs (w : Fin 5 → ℝ) :
    Real.sqrt (∑ i, |w i| ^ 2) ≤ ∑ i, |w i| := by
  rw [show (∑ i, |w i|) = Real.sqrt ((∑ i, |w i|) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_le_sqrt
    (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg (w i))

/-- The Euclidean norm of a vector is at most its `ℓ¹` norm. -/
lemma norm_toLp_le_sum_abs (w : Fin 5 → ℝ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 5))‖ ≤ ∑ i, |w i| := by
  rw [EuclideanSpace.norm_eq]
  simpa only [Real.norm_eq_abs, WithLp.ofLp_toLp] using sqrt_sum_sq_le_sum_abs w

/-- Each coordinate of a Euclidean vector is bounded by its norm. -/
lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) : |x.ofLp i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq,
    show |x.ofLp i| = Real.sqrt (|x.ofLp i| ^ 2) from (Real.sqrt_sq (abs_nonneg _)).symm]
  refine Real.sqrt_le_sqrt ?_
  exact (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)).trans_eq' (by simp [Real.norm_eq_abs])

/-- The `ℓ²` operator norm of a `5 × 5` real matrix is at most its entrywise `ℓ¹` norm. -/
theorem opNorm_le_nrm1 (A : Matrix (Fin 5) (Fin 5) ℝ) : ‖A‖ ≤ nrm1 A := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (nrm1_nonneg A) fun x => ?_
  show ‖(WithLp.toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℝ (Fin 5))‖ ≤ nrm1 A * ‖x‖
  refine (norm_toLp_le_sum_abs _).trans ?_
  rw [nrm1, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine le_trans (by
    simpa [Matrix.mulVec, dotProduct] using
      Finset.abs_sum_le_sum_abs (fun j => A i j * x.ofLp j) Finset.univ) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_left (abs_coord_le_norm x j) (abs_nonneg _)

/-- **Operator-norm convergence for the family `a t`.** -/
theorem Qa_tendsto_Qmin_opNorm :
    Tendsto (fun t : ℕ => ‖Q (avec t) - Qmin‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => opNorm_le_nrm1 _) Qa_tendsto_Qmin

/-- **Operator-norm convergence for the family `b t`.** -/
theorem Qb_tendsto_Qmax_opNorm :
    Tendsto (fun t : ℕ => ‖Q (bvec t) - Qmax‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => opNorm_le_nrm1 _) Qb_tendsto_Qmax

end Brockian.UnbalancedPentagon

import Brockian.LimitMatrices

/-!
# The two extremal families of fibre sizes

* `aN t = (t², 1, t², t, t)` drives the gap to `0`;
* `bN t = (1, 1, t, t², t)` drives the gap to `1`.

This file records their entrywise data and the elementary limit machinery: every quantity we
must control is `√(rational function of 1/t)`, so it is the value at `u = 0` of a function
continuous at `0`, evaluated at `u = 1/t`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- The "gap → 0" family of fibre sizes. -/
def aN (t : ℕ) : Fin 5 → ℕ := ![t ^ 2, 1, t ^ 2, t, t]

/-- The "gap → 1" family of fibre sizes. -/
def bN (t : ℕ) : Fin 5 → ℕ := ![1, 1, t, t ^ 2, t]

/-- Real-valued version of `aN`. -/
def avec (t : ℕ) : Fin 5 → ℝ := fun i => ((aN t i : ℕ) : ℝ)

/-- Real-valued version of `bN`. -/
def bvec (t : ℕ) : Fin 5 → ℝ := fun i => ((bN t i : ℕ) : ℝ)

@[simp] lemma avec_zero (t : ℕ) : avec t 0 = (t : ℝ) ^ 2 := by simp [avec, aN]
@[simp] lemma avec_one (t : ℕ) : avec t 1 = 1 := by simp [avec, aN]
@[simp] lemma avec_two (t : ℕ) : avec t 2 = (t : ℝ) ^ 2 := by simp [avec, aN]
@[simp] lemma avec_three (t : ℕ) : avec t 3 = (t : ℝ) := by simp [avec, aN]
@[simp] lemma avec_four (t : ℕ) : avec t 4 = (t : ℝ) := by simp [avec, aN]

@[simp] lemma bvec_zero (t : ℕ) : bvec t 0 = 1 := by simp [bvec, bN]
@[simp] lemma bvec_one (t : ℕ) : bvec t 1 = 1 := by simp [bvec, bN]
@[simp] lemma bvec_two (t : ℕ) : bvec t 2 = (t : ℝ) := by simp [bvec, bN]
@[simp] lemma bvec_three (t : ℕ) : bvec t 3 = (t : ℝ) ^ 2 := by simp [bvec, bN]
@[simp] lemma bvec_four (t : ℕ) : bvec t 4 = (t : ℝ) := by simp [bvec, bN]

lemma aN_pos {t : ℕ} (ht : 1 ≤ t) (i : Fin 5) : 0 < aN t i := by
  fin_cases i <;> simp [aN] <;> positivity

lemma bN_pos {t : ℕ} (ht : 1 ≤ t) (i : Fin 5) : 0 < bN t i := by
  fin_cases i <;> simp [bN] <;> positivity

lemma avec_pos {t : ℕ} (ht : 1 ≤ t) (i : Fin 5) : 0 < avec t i := by
  simpa [avec] using (aN_pos ht i)

lemma bvec_pos {t : ℕ} (ht : 1 ≤ t) (i : Fin 5) : 0 < bvec t i := by
  simpa [bvec] using (bN_pos ht i)

/-! ### Degrees -/

lemma deg_avec (t : ℕ) :
    deg (avec t) 0 = (t : ℝ) + 1 ∧ deg (avec t) 1 = 2 * (t : ℝ) ^ 2 ∧
    deg (avec t) 2 = 1 + (t : ℝ) ∧ deg (avec t) 3 = (t : ℝ) ^ 2 + (t : ℝ) ∧
    deg (avec t) 4 = (t : ℝ) + (t : ℝ) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp [deg_zero, deg_one, deg_two, deg_three, deg_four]; try ring)

lemma deg_bvec (t : ℕ) :
    deg (bvec t) 0 = (t : ℝ) + 1 ∧ deg (bvec t) 1 = 1 + (t : ℝ) ∧
    deg (bvec t) 2 = 1 + (t : ℝ) ^ 2 ∧ deg (bvec t) 3 = 2 * (t : ℝ) ∧
    deg (bvec t) 4 = (t : ℝ) ^ 2 + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp [deg_zero, deg_one, deg_two, deg_three, deg_four]; try ring)

/-! ### Limit machinery -/

lemma tendsto_natInv : Tendsto (fun t : ℕ => ((t : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- If `f t = g (1/t)` for large `t` and `g` is continuous at `0`, then `f → g 0`. -/
lemma tendsto_of_eq_at_inv {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    (hf : ∀ t : ℕ, 1 ≤ t → f t = g ((t : ℝ)⁻¹)) : Tendsto f atTop (𝓝 (g 0)) := by
  have h1 : Tendsto (fun t : ℕ => g ((t : ℝ)⁻¹)) atTop (𝓝 (g 0)) :=
    hg.tendsto.comp tendsto_natInv
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact (hf t ht).symm

/-- A convenient repackaging: the limit value is given separately. -/
lemma tendsto_of_eq_at_inv' {f : ℕ → ℝ} {g : ℝ → ℝ} {L : ℝ} (hg : ContinuousAt g 0)
    (hL : g 0 = L) (hf : ∀ t : ℕ, 1 ≤ t → f t = g ((t : ℝ)⁻¹)) : Tendsto f atTop (𝓝 L) :=
  hL ▸ tendsto_of_eq_at_inv hg hf

/-- Entrywise convergence of matrices implies convergence of the entrywise `ℓ¹` distance. -/
lemma nrm1_tendsto_zero {A : ℕ → Matrix (Fin 5) (Fin 5) ℝ} {B : Matrix (Fin 5) (Fin 5) ℝ}
    (h : ∀ i j, Tendsto (fun t => A t i j) atTop (𝓝 (B i j))) :
    Tendsto (fun t => nrm1 (A t - B)) atTop (𝓝 0) := by
  have : Tendsto (fun t => ∑ i, ∑ j, |A t i j - B i j|) atTop (𝓝 (∑ i : Fin 5, ∑ j : Fin 5, (0:ℝ))) := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    have := (h i j).sub tendsto_const_nhds (b := B i j)
    simpa using this.abs
  simpa [nrm1] using this

end Brockian.UnbalancedPentagon

import Brockian.Perturb

/-!
# The two limiting matrices

* `Qmin` has nonzero entries only on the edges `{2,3}` and `{4,0}`, both of weight `1`.
  It is the normalized adjacency matrix of a perfect matching on `{2,3}`, `{4,0}` plus an
  isolated vertex `1`; its spectrum is `1, 1, 0, -1, -1`.
* `Qmax` has nonzero entries only on the edges `{2,3}` and `{3,4}`, both of weight `1/√2`.
  It is the normalized adjacency matrix of the path `2 - 3 - 4` plus two isolated vertices;
  its spectrum is `1, 0, 0, 0, -1`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- The `t → ∞` limit of `Q (a t)`: the matching `{2,3} ∪ {4,0}`. -/
def Qmin : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 0, 0, 0, 1;
     0, 0, 0, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 1, 0, 0;
     1, 0, 0, 0, 0]

/-- The `t → ∞` limit of `Q (b t)`: the path `2 - 3 - 4` with edge weights `1/√2`. -/
noncomputable def Qmax : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, Real.sqrt 2 / 2, 0;
     0, 0, Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2;
     0, 0, 0, Real.sqrt 2 / 2, 0]

lemma Qmin_isSymm : Qmin.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qmin]

lemma Qmax_isSymm : Qmax.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qmax]

/-! ### Spectral data of `Qmin` -/

/-- Eigenvectors of `Qmin`: the two-dimensional eigenspace for the eigenvalue `1`. -/
theorem Qmin_mulVec_top (a b : ℝ) : Qmin *ᵥ ![b, 0, a, a, b] = ![b, 0, a, a, b] := by
  funext i
  fin_cases i <;> simp [Qmin, mulVec, dotProduct, Fin.sum_univ_five]

theorem Qmin_mulVec_bot (a b : ℝ) : Qmin *ᵥ ![b, 0, a, -a, -b] = -(1 : ℝ) • ![b, 0, a, -a, -b] := by
  funext i
  fin_cases i <;> simp [Qmin, mulVec, dotProduct, Fin.sum_univ_five]

theorem Qmin_mulVec_zero : Qmin *ᵥ ![0, 1, 0, 0, 0] = (0 : ℝ) • ![(0:ℝ), 1, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [Qmin, mulVec, dotProduct, Fin.sum_univ_five]

/-! ### Spectral data of `Qmax` -/

/-- The top eigenvector direction of `Qmax`. -/
noncomputable def zmax : Fin 5 → ℝ := ![0, 0, 1/2, Real.sqrt 2 / 2, 1/2]

/-- The bottom eigenvector direction of `Qmax`. -/
noncomputable def zmax' : Fin 5 → ℝ := ![0, 0, 1/2, -(Real.sqrt 2 / 2), 1/2]

@[simp] lemma zmax_0 : zmax 0 = 0 := rfl
@[simp] lemma zmax_1 : zmax 1 = 0 := rfl
@[simp] lemma zmax_2 : zmax 2 = 1/2 := rfl
@[simp] lemma zmax_3 : zmax 3 = Real.sqrt 2 / 2 := rfl
@[simp] lemma zmax_4 : zmax 4 = 1/2 := rfl

@[simp] lemma zmax'_0 : zmax' 0 = 0 := rfl
@[simp] lemma zmax'_1 : zmax' 1 = 0 := rfl
@[simp] lemma zmax'_2 : zmax' 2 = 1/2 := rfl
@[simp] lemma zmax'_3 : zmax' 3 = -(Real.sqrt 2 / 2) := rfl
@[simp] lemma zmax'_4 : zmax' 4 = 1/2 := rfl

/-- `Qmax = zmax zmaxᵀ - zmax' zmax'ᵀ`, hence its quadratic form splits as a difference of
two squares. -/
theorem Qmax_form (x : Fin 5 → ℝ) :
    x ⬝ᵥ (Qmax *ᵥ x) = (zmax ⬝ᵥ x) ^ 2 - (zmax' ⬝ᵥ x) ^ 2 := by
  rw [dot_mulVec]
  simp only [Fin.sum_univ_five, dotProduct, zmax, zmax', Qmax]
  norm_num
  ring

theorem Qmax_mulVec_top : Qmax *ᵥ zmax = (1 : ℝ) • zmax := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  funext i
  fin_cases i <;>
    simp [Qmax, zmax, mulVec, dotProduct, Fin.sum_univ_five] <;> nlinarith [h2]

theorem Qmax_mulVec_bot : Qmax *ᵥ zmax' = -(1 : ℝ) • zmax' := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  funext i
  fin_cases i <;>
    simp [Qmax, zmax', mulVec, dotProduct, Fin.sum_univ_five] <;> nlinarith [h2]

end Brockian.UnbalancedPentagon

import Brockian.Gap

/-!
# The Rayleigh definition of the gap is the second eigenvalue

`sec A v` was defined as the supremum of the Rayleigh quotient of `A` over unit vectors
orthogonal to `v`.  Here we prove that when `v` is a nonzero eigenvector of a real symmetric
`5 × 5` matrix `A` for its *largest* eigenvalue, this supremum is exactly the second largest
eigenvalue `Matrix.IsHermitian.eigenvalues₀ 1` of `A`
(`Brockian.UnbalancedPentagon.sec_eq_eigenvalues₀_one`).

Specialising to `A = Q m` and `v = perron m` gives

`gap m = 1 - (Q m).eigenvalues₀ 1`,

i.e. the definition used throughout is the genuine second normalized-Laplacian eigenvalue
(`gap_eq_one_sub_eigenvalues₀_one`).

The proof is elementary: we transport Mathlib's orthonormal eigenbasis into dot-product
language (`exists_eigenbasis`) and then expand vectors in that basis.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Finset

/-! ### An orthonormal eigenbasis in dot-product language -/

/-- Mathlib's orthonormal eigenbasis of a real symmetric `5 × 5` matrix, transported to
plain vectors `Fin 5 → ℝ` and indexed so that the eigenvalues appear in decreasing order. -/
theorem exists_eigenbasis (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.IsHermitian) :
    ∃ E : Fin 5 → (Fin 5 → ℝ),
      (∀ i j, E i ⬝ᵥ E j = if i = j then 1 else 0) ∧
      (∀ j, A *ᵥ E j = hA.eigenvalues₀ j • E j) ∧
      (∀ x : Fin 5 → ℝ, ∑ j, (E j ⬝ᵥ x) • E j = x) := by
  classical
  set σ : Fin (Fintype.card (Fin 5)) ≃ Fin 5 := Fintype.equivOfCardEq (Fintype.card_fin _) with hσ
  set B := hA.eigenvectorBasis.reindex σ.symm with hB
  refine ⟨fun j => ⇑(B j), ?_, ?_, ?_⟩
  · intro i j
    have h := orthonormal_iff_ite.mp B.orthonormal i j
    rw [show inner ℝ (B i) (B j) = ((B i).ofLp) ⬝ᵥ ((B j).ofLp) by
      simp [PiLp.inner_apply, dotProduct, mul_comm]] at h
    exact h
  · intro j
    have h := hA.mulVec_eigenvectorBasis (σ j)
    simpa [hB, Matrix.IsHermitian.eigenvalues, hσ] using h
  · intro x
    have h := B.sum_repr (WithLp.toLp 2 x)
    have h2 : ∀ j, B.repr (WithLp.toLp 2 x) j = (B j : Fin 5 → ℝ) ⬝ᵥ x := by
      intro j
      rw [B.repr_apply_apply]
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    simp only [h2] at h
    simpa using congrArg WithLp.ofLp h

section Basis

variable {A : Matrix (Fin 5) (Fin 5) ℝ} {E : Fin 5 → Fin 5 → ℝ} {lam : Fin 5 → ℝ}

/-- Parseval's identity in the eigenbasis. -/
lemma dot_self_eq_sum_coeff_sq (hcomp : ∀ x : Fin 5 → ℝ, ∑ j, (E j ⬝ᵥ x) • E j = x)
    (x : Fin 5 → ℝ) : x ⬝ᵥ x = ∑ j, (E j ⬝ᵥ x) ^ 2 := by
  nth_rewrite 1 [← hcomp x]
  rw [sum_dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_dotProduct, smul_eq_mul, sq]

/-- Polarised Parseval identity. -/
lemma dot_eq_sum_coeff_mul (hcomp : ∀ x : Fin 5 → ℝ, ∑ j, (E j ⬝ᵥ x) • E j = x)
    (v x : Fin 5 → ℝ) : v ⬝ᵥ x = ∑ j, (E j ⬝ᵥ v) * (E j ⬝ᵥ x) := by
  nth_rewrite 1 [← hcomp v]
  rw [sum_dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_dotProduct, smul_eq_mul]

/-- The Rayleigh form in the eigenbasis. -/
lemma rayleigh_eq_sum_eigen (heig : ∀ j, A *ᵥ E j = lam j • E j)
    (hcomp : ∀ x : Fin 5 → ℝ, ∑ j, (E j ⬝ᵥ x) • E j = x) (x : Fin 5 → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ j, lam j * (E j ⬝ᵥ x) ^ 2 := by
  nth_rewrite 2 [← hcomp x]
  rw [mulVec_sum]
  simp only [mulVec_smul, heig, smul_smul, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

/-- Symmetry lets us move `A` across a dot product. -/
lemma dot_mulVec_symm (hsymm : Aᵀ = A) (u v : Fin 5 → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hsymm]

/-- The eigenbasis coefficients of an eigenvector are supported on the matching eigenvalues. -/
lemma eigen_coeff_eq_zero (hsymm : Aᵀ = A) (heig : ∀ j, A *ᵥ E j = lam j • E j)
    {v : Fin 5 → ℝ} {mu : ℝ} (hv : A *ᵥ v = mu • v) (j : Fin 5) :
    (lam j - mu) * (E j ⬝ᵥ v) = 0 := by
  have h1 : E j ⬝ᵥ (A *ᵥ v) = (A *ᵥ E j) ⬝ᵥ v := dot_mulVec_symm hsymm _ _
  rw [hv, heig j, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
  linarith [h1]

end Basis

/-- A real symmetric matrix, viewed as Hermitian, is a transpose-fixed matrix. -/
lemma transpose_eq_of_isHermitian {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  ext i j
  simpa using congrFun (congrFun hA i) j

lemma dot_self_pos {v : Fin 5 → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hsum : v ⬝ᵥ v = ∑ k, (v k) ^ 2 := by simp [dotProduct, sq]
  rw [hsum]
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))

/-- Every eigenvalue is at most the top ordered eigenvalue. -/
theorem le_eigenvalues₀_zero {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsHermitian)
    {v : Fin 5 → ℝ} {mu : ℝ} (hv : v ≠ 0) (hvA : A *ᵥ v = mu • v) :
    mu ≤ hA.eigenvalues₀ 0 := by
  obtain ⟨E, horth, heig, hcomp⟩ := exists_eigenbasis A hA
  have hsymm := transpose_eq_of_isHermitian hA
  by_contra hcon
  push_neg at hcon
  have hall : ∀ j, E j ⬝ᵥ v = 0 := by
    intro j
    have h := eigen_coeff_eq_zero hsymm heig hvA j
    rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      have hle : hA.eigenvalues₀ j ≤ hA.eigenvalues₀ 0 := hA.eigenvalues₀_antitone (Fin.zero_le j)
      linarith
    · exact h'
  have := dot_self_eq_sum_coeff_sq hcomp v
  rw [Finset.sum_congr rfl (fun j _ => by rw [hall j]; ring : ∀ j ∈ Finset.univ,
    (E j ⬝ᵥ v) ^ 2 = (0:ℝ))] at this
  simp only [Finset.sum_const, smul_zero] at this
  exact absurd this (dot_self_pos hv).ne'

/-- A uniform bound on the Rayleigh form bounds the top ordered eigenvalue. -/
theorem eigenvalues₀_zero_le {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ x : Fin 5 → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)) : hA.eigenvalues₀ 0 ≤ c := by
  obtain ⟨E, horth, heig, hcomp⟩ := exists_eigenbasis A hA
  have h0 : (E 0) ⬝ᵥ (A *ᵥ E 0) = hA.eigenvalues₀ 0 := by
    rw [heig 0, dotProduct_smul, smul_eq_mul, horth 0 0, if_pos rfl, mul_one]
  have h1 : (E 0) ⬝ᵥ (E 0) = 1 := by rw [horth 0 0, if_pos rfl]
  have := h (E 0)
  rw [h0, h1, mul_one] at this
  exact this

/-! ### The main bridge theorem -/

/-- **The Rayleigh definition of `sec` computes the second largest eigenvalue.**
If `v` is a nonzero eigenvector of the real symmetric matrix `A` for its largest eigenvalue,
then the supremum of the Rayleigh quotient over unit vectors orthogonal to `v` is the second
largest eigenvalue of `A`. -/
theorem sec_eq_eigenvalues₀_one {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsHermitian)
    {v : Fin 5 → ℝ} (hv : v ≠ 0) (hvA : A *ᵥ v = hA.eigenvalues₀ 0 • v) :
    sec A v = hA.eigenvalues₀ 1 := by
  obtain ⟨E, horth, heig, hcomp⟩ := exists_eigenbasis A hA
  have hsymm := transpose_eq_of_isHermitian hA
  set lam := hA.eigenvalues₀ with hlam
  have hanti : Antitone lam := hA.eigenvalues₀_antitone
  set d : Fin 5 → ℝ := fun j => E j ⬝ᵥ v with hd
  have hone_le : ∀ j : Fin 5, j ≠ 0 → (1 : Fin 5) ≤ j := by
    intro j hj
    rw [Fin.le_def]
    have : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp only [Fin.val_one]
    omega
  -- In the case of a simple top eigenvalue, `v` is a multiple of `E 0`.
  have hdzero : lam 1 < lam 0 → ∀ j : Fin 5, j ≠ 0 → d j = 0 := by
    intro hlt j hj
    have h := eigen_coeff_eq_zero hsymm heig hvA j
    have hle : lam j ≤ lam 1 := hanti (hone_le j hj)
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by intro hz; nlinarith)
    · exact h'
  have hd0 : lam 1 < lam 0 → d 0 ≠ 0 := by
    intro hlt hz
    have hpar := dot_self_eq_sum_coeff_sq hcomp v
    have hzero : ∀ j ∈ Finset.univ, (E j ⬝ᵥ v) ^ 2 = (0:ℝ) := by
      intro j _
      rcases eq_or_ne j 0 with rfl | hj
      · rw [show E 0 ⬝ᵥ v = d 0 from rfl, hz]; ring
      · rw [show E j ⬝ᵥ v = d j from rfl, hdzero hlt j hj]; ring
    rw [Finset.sum_congr rfl hzero] at hpar
    simp only [Finset.sum_const, smul_zero] at hpar
    exact absurd hpar (dot_self_pos hv).ne'
  -- Upper bound.
  have hub : ∀ x : Fin 5 → ℝ, x ⬝ᵥ x = 1 → v ⬝ᵥ x = 0 → x ⬝ᵥ (A *ᵥ x) ≤ lam 1 := by
    intro x hx hxv
    have hexp := rayleigh_eq_sum_eigen heig hcomp x
    have hpar := dot_self_eq_sum_coeff_sq hcomp x
    have hkey : ∀ j : Fin 5, lam j * (E j ⬝ᵥ x) ^ 2 ≤ lam 1 * (E j ⬝ᵥ x) ^ 2 := by
      intro j
      rcases le_or_gt (lam 0) (lam 1) with hcase | hcase
      · have hle : lam j ≤ lam 1 := by
          rcases eq_or_ne j 0 with rfl | hj
          · exact hcase
          · exact hanti (hone_le j hj)
        nlinarith [sq_nonneg (E j ⬝ᵥ x)]
      · rcases eq_or_ne j 0 with rfl | hj
        · have hc0 : E 0 ⬝ᵥ x = 0 := by
            have hsplit : v ⬝ᵥ x = ∑ j, d j * (E j ⬝ᵥ x) := dot_eq_sum_coeff_mul hcomp v x
            rw [hxv] at hsplit
            rw [Finset.sum_eq_single (0 : Fin 5)] at hsplit
            · exact (mul_eq_zero.mp hsplit.symm).resolve_left (hd0 hcase)
            · intro j _ hj
              rw [hdzero hcase j hj]; ring
            · intro hcontra; exact absurd (Finset.mem_univ (0 : Fin 5)) hcontra
          rw [hc0]; ring_nf; rfl
        · have hle : lam j ≤ lam 1 := hanti (hone_le j hj)
          nlinarith [sq_nonneg (E j ⬝ᵥ x)]
    calc x ⬝ᵥ (A *ᵥ x) = ∑ j, lam j * (E j ⬝ᵥ x) ^ 2 := hexp
      _ ≤ ∑ j, lam 1 * (E j ⬝ᵥ x) ^ 2 := Finset.sum_le_sum fun j _ => hkey j
      _ = lam 1 * (x ⬝ᵥ x) := by rw [hpar, Finset.mul_sum]
      _ = lam 1 := by rw [hx, mul_one]
  -- A test vector attaining `lam 1`.
  have hwitness : ∃ w : Fin 5 → ℝ, v ⬝ᵥ w = 0 ∧ 0 < w ⬝ᵥ w ∧
      w ⬝ᵥ (A *ᵥ w) = lam 1 * (w ⬝ᵥ w) := by
    have hcombo : ∀ a b : ℝ, ((a • E 0 + b • E 1) ⬝ᵥ (a • E 0 + b • E 1) = a ^ 2 + b ^ 2) ∧
        (v ⬝ᵥ (a • E 0 + b • E 1) = a * d 0 + b * d 1) ∧
        ((a • E 0 + b • E 1) ⬝ᵥ (A *ᵥ (a • E 0 + b • E 1))
          = lam 0 * a ^ 2 + lam 1 * b ^ 2) := by
      intro a b
      have h01 : E 0 ⬝ᵥ E 1 = 0 := by rw [horth 0 1]; norm_num
      have h10 : E 1 ⬝ᵥ E 0 = 0 := by rw [horth 1 0]; norm_num
      have h00 : E 0 ⬝ᵥ E 0 = 1 := by rw [horth 0 0, if_pos rfl]
      have h11 : E 1 ⬝ᵥ E 1 = 1 := by rw [horth 1 1, if_pos rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, h00, h11, h01, h10]
        ring
      · have hv0 : v ⬝ᵥ E 0 = d 0 := by rw [hd]; exact dotProduct_comm _ _
        have hv1 : v ⬝ᵥ E 1 = d 1 := by rw [hd]; exact dotProduct_comm _ _
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hv0, hv1]
      · rw [mulVec_add, mulVec_smul, mulVec_smul, heig 0, heig 1]
        simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, h00, h11, h01, h10]
        ring
    rcases le_or_gt (lam 0) (lam 1) with hcase | hcase
    · -- top eigenvalue is degenerate: pick a vector in `span {E 0, E 1} ∩ v^⊥`
      have heq : lam 0 = lam 1 := le_antisymm hcase (hanti (by norm_num))
      by_cases hboth : d 0 = 0 ∧ d 1 = 0
      · obtain ⟨h0, h1⟩ := hboth
        obtain ⟨hn, ho, hr⟩ := hcombo 1 0
        refine ⟨(1 : ℝ) • E 0 + (0 : ℝ) • E 1, ?_, ?_, ?_⟩
        · rw [ho, h0, h1]; ring
        · rw [hn]; norm_num
        · rw [hr, hn, heq]; ring
      · obtain ⟨hn, ho, hr⟩ := hcombo (d 1) (-(d 0))
        refine ⟨(d 1) • E 0 + (-(d 0)) • E 1, ?_, ?_, ?_⟩
        · rw [ho]; ring
        · rw [hn]
          rcases not_and_or.mp hboth with h | h
          · have := pow_pos (abs_pos.mpr h) 2
            nlinarith [sq_nonneg (d 1), sq_abs (d 0)]
          · have := pow_pos (abs_pos.mpr h) 2
            nlinarith [sq_nonneg (d 0), sq_abs (d 1)]
        · rw [hr, hn, heq]; ring
    · -- simple top eigenvalue: `E 1` works
      refine ⟨E 1, ?_, ?_, ?_⟩
      · rw [dotProduct_comm]
        exact hdzero hcase 1 (by decide)
      · rw [horth 1 1, if_pos rfl]; norm_num
      · rw [heig 1, dotProduct_smul, smul_eq_mul, horth 1 1, if_pos rfl]
  obtain ⟨w, hwv, hwpos, hwR⟩ := hwitness
  have hmem := mem_rayleighSet_of_vec (A := A) hwv hwpos
  rw [hwR, mul_div_assoc, div_self hwpos.ne', mul_one] at hmem
  have hbdd : BddAbove (rayleighSet A v) := by
    refine ⟨lam 1, ?_⟩
    rintro r ⟨x, hx, hp, rfl⟩
    exact hub x hx hp
  refine le_antisymm (csSup_le ⟨_, hmem⟩ ?_) (le_csSup hbdd hmem)
  rintro r ⟨x, hx, hp, rfl⟩
  exact hub x hx hp

/-! ### Specialisation to `Q m` -/

variable {m : Fin 5 → ℝ}

lemma Q_isHermitian (m : Fin 5 → ℝ) : (Q m).IsHermitian := by
  ext i j
  simpa using (Q_symm m j i)

/-- The Rayleigh form of `Q m` never exceeds the squared norm. -/
lemma rayleigh_le_dot_self (hm : ∀ i, 0 < m i) (x : Fin 5 → ℝ) :
    x ⬝ᵥ (Q m *ᵥ x) ≤ 1 * (x ⬝ᵥ x) := by
  set y : Fin 5 → ℝ := fun i => x i / perron m i with hy
  have hxy : (fun i => perron m i * y i) = x := perron_mul_div hm x
  have h1 : x ⬝ᵥ x = Ms m y := by rw [← dot_self_y hm y, hxy]
  have h2 : x ⬝ᵥ (Q m *ᵥ x) = Ms m y - En m y := by
    rw [← hxy]; exact rayleigh_y hm y
  have h3 := En_nonneg (fun i => (hm i).le) y
  rw [h1, h2, one_mul]
  linarith

/-- `1` is the largest eigenvalue of `Q m`. -/
theorem eigenvalues₀_zero_Q (hm : ∀ i, 0 < m i) : (Q_isHermitian m).eigenvalues₀ 0 = 1 := by
  refine le_antisymm (eigenvalues₀_zero_le _ (rayleigh_le_dot_self hm)) ?_
  refine le_eigenvalues₀_zero _ (v := perron m) ?_ ?_
  · intro hcon
    have := perron_pos hm 0
    rw [show perron m 0 = (0 : Fin 5 → ℝ) 0 from congrFun hcon 0] at this
    simp at this
  · rw [Q_mulVec_perron hm, one_smul]

/-- **The gap really is `1` minus the second normalized-Laplacian eigenvalue.** -/
theorem gap_eq_one_sub_eigenvalues₀_one (hm : ∀ i, 0 < m i) :
    gap m = 1 - (Q_isHermitian m).eigenvalues₀ 1 := by
  rw [gap]
  congr 1
  refine sec_eq_eigenvalues₀_one (Q_isHermitian m) ?_ ?_
  · intro hcon
    have := perron_pos hm 0
    rw [show perron m 0 = (0 : Fin 5 → ℝ) 0 from congrFun hcon 0] at this
    simp at this
  · rw [eigenvalues₀_zero_Q hm, one_smul]
    exact Q_mulVec_perron hm

end Brockian.UnbalancedPentagon

import Brockian.Rayleigh

/-!
# Workhorse lemmas for the spectral gap

`gap m = 1 - sec (Q m) (perron m)` where `sec` is the supremum of the Rayleigh quotient over
unit vectors orthogonal to the Perron vector.  Via the change of variables of
`Brockian.Rayleigh` this is exactly

`gap m = inf { En m y / Ms m y : Ctr m y = 0, y ≠ 0 }`,

and we provide the two inequalities in usable form.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

/-- Recover the "conductance coordinates" `y` of a vector `x`. -/
lemma perron_mul_div (hm : ∀ i, 0 < m i) (x : Fin 5 → ℝ) :
    (fun i => perron m i * (x i / perron m i)) = x := by
  funext i
  field_simp [perron_ne hm i]

lemma rayleigh_eq_of_unit (hm : ∀ i, 0 < m i) {x : Fin 5 → ℝ} (hx : x ⬝ᵥ x = 1) :
    x ⬝ᵥ (Q m *ᵥ x) = 1 - En m (fun i => x i / perron m i) := by
  have hxy : (fun i => perron m i * (x i / perron m i)) = x := perron_mul_div hm x
  have h1 : Ms m (fun i => x i / perron m i) = 1 := by
    rw [← dot_self_y hm (fun i => x i / perron m i), hxy]; exact hx
  have h2 := rayleigh_y hm (fun i => x i / perron m i)
  rw [hxy, h1] at h2
  exact h2

lemma rayleigh_le_one (hm : ∀ i, 0 < m i) {x : Fin 5 → ℝ} (hx : x ⬝ᵥ x = 1) :
    x ⬝ᵥ (Q m *ᵥ x) ≤ 1 := by
  rw [rayleigh_eq_of_unit hm hx]
  have := En_nonneg (fun i => (hm i).le) (fun i => x i / perron m i)
  linarith

lemma bddAbove_rayleighSet (hm : ∀ i, 0 < m i) :
    BddAbove (rayleighSet (Q m) (perron m)) := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, hx, hp, rfl⟩
  exact rayleigh_le_one hm hx

/-- Every vector orthogonal to `v` contributes its Rayleigh quotient. -/
lemma mem_rayleighSet_of_vec {A : Matrix (Fin 5) (Fin 5) ℝ} {v w : Fin 5 → ℝ}
    (hw : v ⬝ᵥ w = 0) (hpos : 0 < w ⬝ᵥ w) :
    (w ⬝ᵥ (A *ᵥ w)) / (w ⬝ᵥ w) ∈ rayleighSet A v := by
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s * s = w ⬝ᵥ w :=
    ⟨Real.sqrt (w ⬝ᵥ w), Real.sqrt_pos.mpr hpos, Real.mul_self_sqrt hpos.le⟩
  have hcc : s⁻¹ * s⁻¹ * (w ⬝ᵥ w) = 1 := by rw [← hs2]; field_simp
  refine ⟨s⁻¹ • w, ?_, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]; exact hcc
  · rw [dotProduct_smul, smul_eq_mul, hw, mul_zero]
  · rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      div_eq_iff hpos.ne']
    linear_combination (-(w ⬝ᵥ (A *ᵥ w))) * hcc

/-- Any vector orthogonal to the Perron vector gives a lower bound on `sec`. -/
lemma le_sec_of_vec (hm : ∀ i, 0 < m i) {w : Fin 5 → ℝ}
    (hw : perron m ⬝ᵥ w = 0) (hpos : 0 < w ⬝ᵥ w) :
    (w ⬝ᵥ (Q m *ᵥ w)) / (w ⬝ᵥ w) ≤ sec (Q m) (perron m) :=
  le_csSup (bddAbove_rayleighSet hm) (mem_rayleighSet_of_vec hw hpos)

lemma nonempty_rayleighSet (hm : ∀ i, 0 < m i) :
    (rayleighSet (Q m) (perron m)).Nonempty := by
  have h0 := wt_pos hm 0
  have h1 := wt_pos hm 1
  set y : Fin 5 → ℝ := ![wt m 1, -(wt m 0), 0, 0, 0] with hy
  have hCtr : Ctr m y = 0 := by rw [Ctr_eq]; simp [hy]; ring
  have hMs : 0 < Ms m y := by
    rw [Ms_eq]; simp only [hy]; norm_num
    have h2 := wt_pos hm 2
    have h3 := wt_pos hm 3
    have h4 := wt_pos hm 4
    positivity
  refine ⟨_, mem_rayleighSet_of_vec (w := fun i => perron m i * y i) ?_ ?_⟩
  · rw [dot_perron_y hm y]; exact hCtr
  · rw [dot_self_y hm y]; exact hMs

lemma sec_le_of (hm : ∀ i, 0 < m i) {c : ℝ}
    (h : ∀ x : Fin 5 → ℝ, x ⬝ᵥ x = 1 → perron m ⬝ᵥ x = 0 → x ⬝ᵥ (Q m *ᵥ x) ≤ c) :
    sec (Q m) (perron m) ≤ c := by
  refine csSup_le (nonempty_rayleighSet hm) ?_
  rintro r ⟨x, hx, hp, rfl⟩
  exact h x hx hp

/-! ### The `y`-coordinate versions -/

/-- Upper bound for the gap from a single test function `y` with zero weighted mean. -/
theorem gap_le_of_test (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ)
    (hC : Ctr m y = 0) (hM : 0 < Ms m y) : gap m ≤ En m y / Ms m y := by
  have hww : (fun i => perron m i * y i) ⬝ᵥ (fun i => perron m i * y i) = Ms m y :=
    dot_self_y hm y
  have h1 : perron m ⬝ᵥ (fun i => perron m i * y i) = 0 := by rw [dot_perron_y hm y]; exact hC
  have h2 : 0 < (fun i => perron m i * y i) ⬝ᵥ (fun i => perron m i * y i) := by
    rw [hww]; exact hM
  have h4 := le_sec_of_vec hm h1 h2
  rw [rayleigh_y hm y, hww] at h4
  have h5 : (Ms m y - En m y) / Ms m y = 1 - En m y / Ms m y := by field_simp
  rw [h5] at h4
  rw [gap]; linarith

/-- Lower bound for the gap from a weighted Poincaré inequality. -/
theorem le_gap_of_poincare (hm : ∀ i, 0 < m i) {c : ℝ}
    (h : ∀ y : Fin 5 → ℝ, Ctr m y = 0 → c * Ms m y ≤ En m y) : c ≤ gap m := by
  rw [gap]
  have hsec : sec (Q m) (perron m) ≤ 1 - c := by
    refine sec_le_of hm ?_
    intro x hx hp
    have hxy : (fun i => perron m i * (x i / perron m i)) = x := perron_mul_div hm x
    have hMs : Ms m (fun i => x i / perron m i) = 1 := by
      rw [← dot_self_y hm (fun i => x i / perron m i), hxy]; exact hx
    have hCtr : Ctr m (fun i => x i / perron m i) = 0 := by
      rw [← dot_perron_y hm (fun i => x i / perron m i), hxy]; exact hp
    have hh := h _ hCtr
    rw [hMs, mul_one] at hh
    rw [rayleigh_eq_of_unit hm hx]
    linarith
  linarith

lemma gap_nonneg (hm : ∀ i, 0 < m i) : 0 ≤ gap m := by
  refine le_gap_of_poincare hm ?_
  intro y _
  simpa using En_nonneg (fun i => (hm i).le) y

end Brockian.UnbalancedPentagon

import Brockian.Defs

/-!
# The Rayleigh quotient of `Q m` in "conductance" coordinates

Writing a vector `x` as `x i = perron m i * y i` turns the Rayleigh quotient of `Q m`
into the classical weighted Poincaré quotient of the 5-cycle:

* `x ⬝ᵥ x = Ms m y = ∑ i, D i * (y i)^2`,
* `perron m ⬝ᵥ x = Ctr m y = ∑ i, D i * y i`,
* `x ⬝ᵥ (Q m *ᵥ x) = Ms m y - En m y` with `En m y = ∑_{edges} m i * m j * (y i - y j)^2`.

Consequently the spectral gap is
`gap m = inf { En m y : Ms m y = 1, Ctr m y = 0 }`,
and we record the two directions of that description as usable lemmas.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

lemma dot_mulVec (A : Matrix (Fin 5) (Fin 5) ℝ) (x : Fin 5 → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, A i j * x i * x j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma Adj_symm {i j : Fin 5} (h : Adj i j) : Adj j i := by
  revert h; revert i j; decide

lemma Q_symm (m : Fin 5 → ℝ) (i j : Fin 5) : Q m i j = Q m j i := by
  by_cases h : Adj i j
  · rw [Q, Q, if_pos h, if_pos (Adj_symm h)]; ring_nf
  · rw [Q, Q, if_neg h, if_neg (fun hc => h (Adj_symm hc))]

lemma Q_isSymm (m : Fin 5 → ℝ) : (Q m).IsSymm := by
  ext i j; exact (Q_symm m j i)

lemma Qp_mul (hm : ∀ i, 0 < m i) (i j : Fin 5) :
    Q m i j * (perron m i * perron m j) = if Adj i j then m i * m j else 0 := by
  have hdi := deg_pos hm i
  have hdj := deg_pos hm j
  have hmi := hm i
  have hmj := hm j
  by_cases h : Adj i j
  · simp only [Q, perron, if_pos h]
    have hA : (0:ℝ) ≤ m i * m j / (deg m i * deg m j) :=
      div_nonneg (by nlinarith) (by nlinarith)
    have hB : (0:ℝ) ≤ wt m i := (wt_pos hm i).le
    have hC : (0:ℝ) ≤ wt m j := (wt_pos hm j).le
    rw [← Real.sqrt_mul hB, ← Real.sqrt_mul hA]
    have hkey : m i * m j / (deg m i * deg m j) * (wt m i * wt m j) = (m i * m j) ^ 2 := by
      simp only [wt]; field_simp
    rw [hkey, Real.sqrt_sq (by nlinarith)]
  · simp [Q, h]

/-- Sum of the adjacency-indicator against any function: `∑ j, [i ~ j] f j = f (i-1) + f (i+1)`. -/
lemma sum_adj (f : Fin 5 → ℝ) (i : Fin 5) :
    ∑ j, (if Adj i j then f j else 0) = f (i - 1) + f (i + 1) := by
  fin_cases i <;>
    simp [Fin.sum_univ_five, Adj, show ¬ ((0:Fin 5) = 1) by decide] <;> ring

lemma perron_ne (hm : ∀ i, 0 < m i) (i : Fin 5) : perron m i ≠ 0 := (perron_pos hm i).ne'

/-- The Perron vector is an eigenvector of `Q m` for the eigenvalue `1`. -/
theorem Q_mulVec_perron (hm : ∀ i, 0 < m i) : Q m *ᵥ perron m = perron m := by
  funext i
  have hpi := perron_pos hm i
  have key : ∀ j, Q m i j * perron m j = (if Adj i j then m i * m j else 0) / perron m i := by
    intro j
    rw [eq_div_iff hpi.ne']
    have := Qp_mul hm i j
    linarith [this, (by ring : Q m i j * perron m j * perron m i
      = Q m i j * (perron m i * perron m j))]
  simp only [mulVec, dotProduct, key]
  rw [← Finset.sum_div]
  have : ∑ j, (if Adj i j then m i * m j else 0) = m i * deg m i := by
    have := sum_adj (fun j => m i * m j) i
    simpa [deg, mul_add] using this
  rw [this]
  rw [eq_comm, eq_div_iff hpi.ne']
  have : perron m i * perron m i = wt m i := perron_sq hm i
  rw [this]; rfl

/-! ### Change of variables -/

lemma dot_self_y (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ) :
    (fun i => perron m i * y i) ⬝ᵥ (fun i => perron m i * y i) = Ms m y := by
  simp only [dotProduct, Ms]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := perron_sq hm i
  calc perron m i * y i * (perron m i * y i) = (perron m i * perron m i) * y i ^ 2 := by ring
    _ = wt m i * y i ^ 2 := by rw [h]

lemma dot_perron_y (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ) :
    perron m ⬝ᵥ (fun i => perron m i * y i) = Ctr m y := by
  simp only [dotProduct, Ctr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := perron_sq hm i
  calc perron m i * (perron m i * y i) = (perron m i * perron m i) * y i := by ring
    _ = wt m i * y i := by rw [h]

lemma energy_identity (m y : Fin 5 → ℝ) :
    ∑ i, ∑ j, (if Adj i j then m i * m j else 0) * (y i * y j) = Ms m y - En m y := by
  have h : ∀ i : Fin 5, ∑ j, (if Adj i j then m i * m j else 0) * (y i * y j)
      = ∑ j, (if Adj i j then (fun j => m i * m j * (y i * y j)) j else 0) := by
    intro i
    exact Finset.sum_congr rfl fun j _ => by by_cases h : Adj i j <;> simp [h]
  simp only [h, sum_adj]
  rw [En_eq, Ms_eq, Fin.sum_univ_five]
  simp only [wt, deg_zero, deg_one, deg_two, deg_three, deg_four]
  simp only [Fin5.add_one_0, Fin5.add_one_1, Fin5.add_one_2, Fin5.add_one_3, Fin5.add_one_4,
    Fin5.sub_one_0, Fin5.sub_one_1, Fin5.sub_one_2, Fin5.sub_one_3, Fin5.sub_one_4]
  ring

lemma rayleigh_y (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ) :
    (fun i => perron m i * y i) ⬝ᵥ (Q m *ᵥ (fun i => perron m i * y i)) = Ms m y - En m y := by
  rw [dot_mulVec]
  rw [← energy_identity m y]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := Qp_mul hm i j
  calc Q m i j * (perron m i * y i) * (perron m j * y j)
      = (Q m i j * (perron m i * perron m j)) * (y i * y j) := by ring
    _ = _ := by rw [this]

end Brockian.UnbalancedPentagon

import Brockian.FamilyDefs

/-!
# Entrywise limits for the family `b t = (1, 1, t, t², t)`

With `d = (t+1, 1+t, 1+t², 2t, t²+1)` the nonzero entries of `Q (b t)` are, for `t ≥ 1`,

* `Q (b t) 0 1 = 1/(t+1)`,
* `Q (b t) 1 2 = √(t/((1+t)(1+t²)))`,
* `Q (b t) 2 3 = √(t²/(2(1+t²)))`,
* `Q (b t) 3 4 = √(t²/(2(1+t²)))`,
* `Q (b t) 4 0 = √(t/((1+t²)(1+t)))`,

together with the symmetric ones; so `Q (b t) → Qmax` entrywise.

The Perron vector is `p i = √(D i)` with `D = (t+1, 1+t, t+t³, 2t³, t³+t)`; rescaled by
`cb t = 1/√(4t³)` it converges to `zmax = (0, 0, 1/2, √2/2, 1/2)`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

private lemma tposB {t : ℕ} (ht : 1 ≤ t) : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht

lemma sqrt_half : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, h2]; norm_num
  rw [← h, Real.sqrt_sq (by positivity)]

lemma inv_sqrt_two : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith [h2]

lemma sqrt_quarter : Real.sqrt (1 / 4) = 1 / 2 := by
  rw [show (1:ℝ) / 4 = (1 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ### Entry formulas -/

section Entries

variable {t : ℕ}

lemma Qb_01_eq (ht : 1 ≤ t) :
    Q (bvec t) 0 1 = Real.sqrt ((t : ℝ)⁻¹ ^ 2 / (1 + (t : ℝ)⁻¹) ^ 2) := by
  have h := tposB ht
  obtain ⟨d0, d1, _, _, _⟩ := deg_bvec t
  rw [Q_apply_of_adj (by decide : Adj (0 : Fin 5) 1), d0, d1]
  congr 1
  simp only [bvec_zero, bvec_one]
  field_simp
  ring

lemma Qb_12_eq (ht : 1 ≤ t) :
    Q (bvec t) 1 2
      = Real.sqrt ((t : ℝ)⁻¹ ^ 2 / ((1 + (t : ℝ)⁻¹) * (1 + (t : ℝ)⁻¹ ^ 2))) := by
  have h := tposB ht
  obtain ⟨_, d1, d2, _, _⟩ := deg_bvec t
  rw [Q_apply_of_adj (by decide : Adj (1 : Fin 5) 2), d1, d2]
  congr 1
  simp only [bvec_one, bvec_two]
  field_simp
  ring

lemma Qb_23_eq (ht : 1 ≤ t) :
    Q (bvec t) 2 3 = Real.sqrt (1 / (2 * (1 + (t : ℝ)⁻¹ ^ 2))) := by
  have h := tposB ht
  obtain ⟨_, _, d2, d3, _⟩ := deg_bvec t
  rw [Q_apply_of_adj (by decide : Adj (2 : Fin 5) 3), d2, d3]
  congr 1
  simp only [bvec_two, bvec_three]
  field_simp
  ring

lemma Qb_34_eq (ht : 1 ≤ t) :
    Q (bvec t) 3 4 = Real.sqrt (1 / (2 * (1 + (t : ℝ)⁻¹ ^ 2))) := by
  have h := tposB ht
  obtain ⟨_, _, _, d3, d4⟩ := deg_bvec t
  rw [Q_apply_of_adj (by decide : Adj (3 : Fin 5) 4), d3, d4]
  congr 1
  simp only [bvec_three, bvec_four]
  field_simp

lemma Qb_40_eq (ht : 1 ≤ t) :
    Q (bvec t) 4 0
      = Real.sqrt ((t : ℝ)⁻¹ ^ 2 / ((1 + (t : ℝ)⁻¹ ^ 2) * (1 + (t : ℝ)⁻¹))) := by
  have h := tposB ht
  obtain ⟨d0, _, _, _, d4⟩ := deg_bvec t
  rw [Q_apply_of_adj (by decide : Adj (4 : Fin 5) 0), d4, d0]
  congr 1
  simp only [bvec_four, bvec_zero]
  field_simp

end Entries

/-! ### Continuity of the profile functions -/

lemma contAt_profB1 : ContinuousAt (fun u : ℝ => Real.sqrt (u ^ 2 / (1 + u) ^ 2)) 0 := by
  have h : ContinuousAt (fun u : ℝ => u ^ 2 / (1 + u) ^ 2) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  exact Real.continuous_sqrt.continuousAt.comp h

lemma contAt_profB2 :
    ContinuousAt (fun u : ℝ => Real.sqrt (u ^ 2 / ((1 + u) * (1 + u ^ 2)))) 0 := by
  have h : ContinuousAt (fun u : ℝ => u ^ 2 / ((1 + u) * (1 + u ^ 2))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  exact Real.continuous_sqrt.continuousAt.comp h

lemma contAt_profB3 : ContinuousAt (fun u : ℝ => Real.sqrt (1 / (2 * (1 + u ^ 2)))) 0 := by
  have h : ContinuousAt (fun u : ℝ => 1 / (2 * (1 + u ^ 2))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  exact Real.continuous_sqrt.continuousAt.comp h

lemma contAt_profB4 :
    ContinuousAt (fun u : ℝ => Real.sqrt (u ^ 2 / ((1 + u ^ 2) * (1 + u)))) 0 := by
  have h : ContinuousAt (fun u : ℝ => u ^ 2 / ((1 + u ^ 2) * (1 + u))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  exact Real.continuous_sqrt.continuousAt.comp h

/-! ### Entrywise limits -/

lemma Qb_01_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 0 1) atTop (𝓝 0) :=
  tendsto_of_eq_at_inv' contAt_profB1 (by norm_num) fun _ ht => Qb_01_eq ht

lemma Qb_12_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 1 2) atTop (𝓝 0) :=
  tendsto_of_eq_at_inv' contAt_profB2 (by norm_num) fun _ ht => Qb_12_eq ht

lemma Qb_23_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 2 3) atTop (𝓝 (Real.sqrt 2 / 2)) :=
  tendsto_of_eq_at_inv' contAt_profB3 (by norm_num [inv_sqrt_two]) fun _ ht => Qb_23_eq ht

lemma Qb_34_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 3 4) atTop (𝓝 (Real.sqrt 2 / 2)) :=
  tendsto_of_eq_at_inv' contAt_profB3 (by norm_num [inv_sqrt_two]) fun _ ht => Qb_34_eq ht

lemma Qb_40_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 4 0) atTop (𝓝 0) :=
  tendsto_of_eq_at_inv' contAt_profB4 (by norm_num) fun _ ht => Qb_40_eq ht

lemma Qb_10_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 1 0) atTop (𝓝 0) := by
  have h : (fun t : ℕ => Q (bvec t) 1 0) = fun t : ℕ => Q (bvec t) 0 1 :=
    funext fun t => Q_symm _ 1 0
  rw [h]; exact Qb_01_tendsto

lemma Qb_21_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 2 1) atTop (𝓝 0) := by
  have h : (fun t : ℕ => Q (bvec t) 2 1) = fun t : ℕ => Q (bvec t) 1 2 :=
    funext fun t => Q_symm _ 2 1
  rw [h]; exact Qb_12_tendsto

lemma Qb_32_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 3 2) atTop (𝓝 (Real.sqrt 2 / 2)) := by
  have h : (fun t : ℕ => Q (bvec t) 3 2) = fun t : ℕ => Q (bvec t) 2 3 :=
    funext fun t => Q_symm _ 3 2
  rw [h]; exact Qb_23_tendsto

lemma Qb_43_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 4 3) atTop (𝓝 (Real.sqrt 2 / 2)) := by
  have h : (fun t : ℕ => Q (bvec t) 4 3) = fun t : ℕ => Q (bvec t) 3 4 :=
    funext fun t => Q_symm _ 4 3
  rw [h]; exact Qb_34_tendsto

lemma Qb_04_tendsto : Tendsto (fun t : ℕ => Q (bvec t) 0 4) atTop (𝓝 0) := by
  have h : (fun t : ℕ => Q (bvec t) 0 4) = fun t : ℕ => Q (bvec t) 4 0 :=
    funext fun t => Q_symm _ 0 4
  rw [h]; exact Qb_40_tendsto

lemma Qb_zero_entry {i j : Fin 5} (h : ¬ Adj i j) (h2 : Qmax i j = 0) :
    Tendsto (fun t : ℕ => Q (bvec t) i j) atTop (𝓝 (Qmax i j)) := by
  simp only [Q_apply_of_not_adj h, h2]
  exact tendsto_const_nhds

/-- Entrywise convergence `Q (b t) → Qmax`. -/
theorem Qb_entry_tendsto (i j : Fin 5) :
    Tendsto (fun t : ℕ => Q (bvec t) i j) atTop (𝓝 (Qmax i j)) := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact Qb_zero_entry (by decide) rfl
      | exact Qb_01_tendsto
      | exact Qb_10_tendsto
      | exact Qb_12_tendsto
      | exact Qb_21_tendsto
      | exact Qb_23_tendsto
      | exact Qb_32_tendsto
      | exact Qb_34_tendsto
      | exact Qb_43_tendsto
      | exact Qb_40_tendsto
      | exact Qb_04_tendsto

/-- **Target 4 (convergence).** `Q (b t) → Qmax` in the entrywise `ℓ¹` norm. -/
theorem Qb_tendsto_Qmax : Tendsto (fun t : ℕ => nrm1 (Q (bvec t) - Qmax)) atTop (𝓝 0) :=
  nrm1_tendsto_zero Qb_entry_tendsto

/-! ### The Perron direction -/

/-- Normalising factor for the Perron vector of `b t`. -/
noncomputable def cb (t : ℕ) : ℝ := (Real.sqrt (4 * (t : ℝ) ^ 3))⁻¹

lemma wt_bvec (t : ℕ) :
    wt (bvec t) 0 = (t : ℝ) + 1 ∧ wt (bvec t) 1 = 1 + (t : ℝ) ∧
    wt (bvec t) 2 = (t : ℝ) * (1 + (t : ℝ) ^ 2) ∧ wt (bvec t) 3 = 2 * (t : ℝ) ^ 3 ∧
    wt (bvec t) 4 = (t : ℝ) * ((t : ℝ) ^ 2 + 1) := by
  obtain ⟨d0, d1, d2, d3, d4⟩ := deg_bvec t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [wt, d0, d1, d2, d3, d4]; simp; try ring)

lemma cb_perron_eq {t : ℕ} (ht : 1 ≤ t) (i : Fin 5) :
    cb t * perron (bvec t) i = Real.sqrt (wt (bvec t) i / (4 * (t : ℝ) ^ 3)) := by
  have h := tposB ht
  have hw : 0 ≤ wt (bvec t) i := (wt_pos (bvec_pos ht) i).le
  rw [cb, perron, Real.sqrt_div hw, div_eq_mul_inv, mul_comm]

lemma cb_perron_0_eq {t : ℕ} (ht : 1 ≤ t) :
    cb t * perron (bvec t) 0
      = Real.sqrt (((t : ℝ)⁻¹ ^ 3 + (t : ℝ)⁻¹ ^ 2) / 4) := by
  have h := tposB ht
  obtain ⟨w0, _, _, _, _⟩ := wt_bvec t
  rw [cb_perron_eq ht 0, w0]
  congr 1
  field_simp
  ring

lemma cb_perron_1_eq {t : ℕ} (ht : 1 ≤ t) :
    cb t * perron (bvec t) 1
      = Real.sqrt (((t : ℝ)⁻¹ ^ 3 + (t : ℝ)⁻¹ ^ 2) / 4) := by
  have h := tposB ht
  obtain ⟨_, w1, _, _, _⟩ := wt_bvec t
  rw [cb_perron_eq ht 1, w1]
  congr 1
  field_simp

lemma cb_perron_2_eq {t : ℕ} (ht : 1 ≤ t) :
    cb t * perron (bvec t) 2 = Real.sqrt (((t : ℝ)⁻¹ ^ 2 + 1) / 4) := by
  have h := tposB ht
  obtain ⟨_, _, w2, _, _⟩ := wt_bvec t
  rw [cb_perron_eq ht 2, w2]
  congr 1
  field_simp

lemma cb_perron_3_eq {t : ℕ} (ht : 1 ≤ t) :
    cb t * perron (bvec t) 3 = Real.sqrt (1 / 2) := by
  have h := tposB ht
  obtain ⟨_, _, _, w3, _⟩ := wt_bvec t
  rw [cb_perron_eq ht 3, w3]
  congr 1
  field_simp
  ring

lemma cb_perron_4_eq {t : ℕ} (ht : 1 ≤ t) :
    cb t * perron (bvec t) 4 = Real.sqrt ((1 + (t : ℝ)⁻¹ ^ 2) / 4) := by
  have h := tposB ht
  obtain ⟨_, _, _, _, w4⟩ := wt_bvec t
  rw [cb_perron_eq ht 4, w4]
  congr 1
  field_simp

lemma contAt_profP1 : ContinuousAt (fun u : ℝ => Real.sqrt ((u ^ 3 + u ^ 2) / 4)) 0 := by
  have h : ContinuousAt (fun u : ℝ => (u ^ 3 + u ^ 2) / 4) 0 := by fun_prop
  exact Real.continuous_sqrt.continuousAt.comp h

lemma contAt_profP2 : ContinuousAt (fun u : ℝ => Real.sqrt ((u ^ 2 + 1) / 4)) 0 := by
  have h : ContinuousAt (fun u : ℝ => (u ^ 2 + 1) / 4) 0 := by fun_prop
  exact Real.continuous_sqrt.continuousAt.comp h

lemma contAt_profP3 : ContinuousAt (fun u : ℝ => Real.sqrt ((1 + u ^ 2) / 4)) 0 := by
  have h : ContinuousAt (fun u : ℝ => (1 + u ^ 2) / 4) 0 := by fun_prop
  exact Real.continuous_sqrt.continuousAt.comp h

lemma perron_b_0_tendsto : Tendsto (fun t : ℕ => cb t * perron (bvec t) 0) atTop (𝓝 (zmax 0)) :=
  tendsto_of_eq_at_inv' contAt_profP1 (by norm_num) fun _ ht => cb_perron_0_eq ht

lemma perron_b_1_tendsto : Tendsto (fun t : ℕ => cb t * perron (bvec t) 1) atTop (𝓝 (zmax 1)) :=
  tendsto_of_eq_at_inv' contAt_profP1 (by norm_num) fun _ ht => cb_perron_1_eq ht

lemma perron_b_2_tendsto : Tendsto (fun t : ℕ => cb t * perron (bvec t) 2) atTop (𝓝 (zmax 2)) :=
  tendsto_of_eq_at_inv' contAt_profP2 (by norm_num [sqrt_quarter]) fun _ ht =>
    cb_perron_2_eq ht

lemma perron_b_3_tendsto : Tendsto (fun t : ℕ => cb t * perron (bvec t) 3) atTop (𝓝 (zmax 3)) := by
  have h : Tendsto (fun t : ℕ => cb t * perron (bvec t) 3) atTop (𝓝 (Real.sqrt (1/2))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (cb_perron_3_eq ht).symm
  have hz : zmax 3 = Real.sqrt (1 / 2) := by rw [zmax_3, sqrt_half]
  rw [hz]; exact h

lemma perron_b_4_tendsto : Tendsto (fun t : ℕ => cb t * perron (bvec t) 4) atTop (𝓝 (zmax 4)) :=
  tendsto_of_eq_at_inv' contAt_profP3 (by norm_num [sqrt_quarter]) fun _ ht =>
    cb_perron_4_eq ht

/-- The normalised Perron vector of `b t` converges to the top eigenvector of `Qmax`. -/
theorem perron_b_entry_tendsto (i : Fin 5) :
    Tendsto (fun t : ℕ => cb t * perron (bvec t) i) atTop (𝓝 (zmax i)) := by
  fin_cases i <;>
    first
      | exact perron_b_0_tendsto
      | exact perron_b_1_tendsto
      | exact perron_b_2_tendsto
      | exact perron_b_3_tendsto
      | exact perron_b_4_tendsto

/-- The squared `ℓ²` distance from the normalised Perron direction to `zmax` tends to `0`. -/
theorem perron_b_approx_tendsto :
    Tendsto (fun t : ℕ => ∑ i, (zmax i - cb t * perron (bvec t) i) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℕ => ∑ i, (zmax i - cb t * perron (bvec t) i) ^ 2) atTop
      (𝓝 (∑ _i : Fin 5, (0:ℝ))) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    have h1 := (tendsto_const_nhds (x := zmax i) (f := atTop (α := ℕ))).sub
      (perron_b_entry_tendsto i)
    simpa using h1.pow 2
  simpa using h

end Brockian.UnbalancedPentagon

import Brockian.Defs

/-!
# The sharp Poincaré inequality on the unweighted 5-cycle

The second eigenvalue of the (unnormalized) Laplacian of `C₅` is `2 - 2 cos (2π/5) = (5-√5)/2`.
We prove the corresponding Poincaré inequality by an explicit sum-of-squares certificate:
if `M = L - κ·I + (κ/5)·J` with `κ = (5-√5)/2`, then `M² = √5 · M`, so that the quadratic
form of `M` equals `‖M y‖² / √5 ≥ 0`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Finset

/-- `g5 = (5 - √5)/4 = 1 - cos (2π/5)`, the second eigenvalue of the normalized Laplacian
of the balanced pentagon. -/
noncomputable def g5 : ℝ := (5 - Real.sqrt 5) / 4

lemma sqrt5_lt_five : Real.sqrt 5 < 5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

lemma one_lt_sqrt5 : 1 < Real.sqrt 5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

lemma g5_pos : 0 < g5 := by simp only [g5]; linarith [sqrt5_lt_five]

lemma g5_lt_one : g5 < 1 := by simp only [g5]; linarith [one_lt_sqrt5]

set_option maxHeartbeats 1000000 in
/-- The sum-of-squares certificate behind the `C₅` Poincaré inequality. -/
lemma c5_sos (s a b c d e : ℝ) (hs : s ^ 2 = 5) (hs0 : 0 < s) :
    0 ≤ ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - e) ^ 2 + (e - a) ^ 2)
      - ((5 - s) / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)
      + ((5 - s) / 10) * (a + b + c + d + e) ^ 2 := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F =
      ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - e) ^ 2 + (e - a) ^ 2)
      - ((5 - s) / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)
      + ((5 - s) / 10) * (a + b + c + d + e) ^ 2 := ⟨_, rfl⟩
  rw [← hF]
  have key : (4 * s * a - (5 + s) * (e + b) + (5 - s) * (d + c)) ^ 2
      + (4 * s * b - (5 + s) * (a + c) + (5 - s) * (e + d)) ^ 2
      + (4 * s * c - (5 + s) * (b + d) + (5 - s) * (a + e)) ^ 2
      + (4 * s * d - (5 + s) * (c + e) + (5 - s) * (b + a)) ^ 2
      + (4 * s * e - (5 + s) * (d + a) + (5 - s) * (c + b)) ^ 2 = 100 * s * F := by
    rw [hF]
    linear_combination (5 * (a + b + c + d + e) ^ 2
      - 25 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)) * hs
  have h1 : (0:ℝ) ≤ 100 * s * F := by rw [← key]; positivity
  nlinarith [h1, hs0]

/-- **Poincaré inequality for `C₅`** in homogeneous form:
`2 g₅ ∑ y i ^ 2 ≤ ∑ (y i - y (i+1))^2 + (2 g₅ / 5) (∑ y i)^2`. -/
theorem c5_poincare (y : Fin 5 → ℝ) :
    2 * g5 * (∑ i, (y i) ^ 2) ≤ (∑ i, (y i - y (i + 1)) ^ 2) + (2 * g5 / 5) * (∑ i, y i) ^ 2 := by
  have hs0 : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have H := c5_sos (Real.sqrt 5) (y 0) (y 1) (y 2) (y 3) (y 4) hs hs0
  simp only [Fin.sum_univ_five, Fin5.add_one_0, Fin5.add_one_1, Fin5.add_one_2,
    Fin5.add_one_3, Fin5.add_one_4, g5]
  linarith [H]

/-- Centered form: if `∑ y i = 0` then `2 g₅ ∑ y i ^ 2 ≤ ∑ (y i - y (i+1))^2`. -/
theorem c5_poincare_centered {y : Fin 5 → ℝ} (hy : (∑ i, y i) = 0) :
    2 * g5 * (∑ i, (y i) ^ 2) ≤ ∑ i, (y i - y (i + 1)) ^ 2 := by
  have := c5_poincare y
  rw [hy] at this
  simpa using this

end Brockian.UnbalancedPentagon

import Brockian.LimitA
import Brockian.LimitB
import Brockian.Perturb
import Brockian.LtOne
import Brockian.LowerBound

/-!
# The two extremal limits of the spectral gap

* `gap_tendsto_zero`: `gap (a t) → 0`, because `Q (a t) → Qmin` and `Qmin` has a
  two-dimensional eigenspace for its top eigenvalue `1`, so some direction orthogonal to the
  Perron vector of `a t` is almost fixed by `Q (a t)`.
* `gap_tendsto_one`: `gap (b t) → 1`, because `Q (b t) → Qmax`, whose quadratic form is
  `(zmax ⬝ x)² - (zmax' ⬝ x)²`, and the Perron direction of `b t` converges to `zmax`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- For the family `a t` the gap is at most the entrywise distance from `Q (a t)` to `Qmin`. -/
theorem gap_avec_le (t : ℕ) (ht : 1 ≤ t) : gap (avec t) ≤ nrm1 (Q (avec t) - Qmin) := by
  have hpos := avec_pos ht
  have p0 := perron_pos hpos 0
  have p2 := perron_pos hpos 2
  have p3 := perron_pos hpos 3
  have p4 := perron_pos hpos 4
  set α : ℝ := perron (avec t) 0 + perron (avec t) 4 with hα
  set β : ℝ := -(perron (avec t) 2 + perron (avec t) 3) with hβ
  have hαpos : 0 < α := by rw [hα]; linarith
  refine gap_le_nrm1_of_eigen hpos (v := ![β, 0, α, α, β]) ?_ ?_ (Qmin_mulVec_top α β)
  · have e0 : (![β, 0, α, α, β] : Fin 5 → ℝ) 0 = β := rfl
    have e1 : (![β, 0, α, α, β] : Fin 5 → ℝ) 1 = 0 := rfl
    have e2 : (![β, 0, α, α, β] : Fin 5 → ℝ) 2 = α := rfl
    have e3 : (![β, 0, α, α, β] : Fin 5 → ℝ) 3 = α := rfl
    have e4 : (![β, 0, α, α, β] : Fin 5 → ℝ) 4 = β := rfl
    simp only [dotProduct, Fin.sum_univ_five, e0, e1, e2, e3, e4]
    rw [hα, hβ]; ring
  · have e0 : (![β, 0, α, α, β] : Fin 5 → ℝ) 0 = β := rfl
    have e1 : (![β, 0, α, α, β] : Fin 5 → ℝ) 1 = 0 := rfl
    have e2 : (![β, 0, α, α, β] : Fin 5 → ℝ) 2 = α := rfl
    have e3 : (![β, 0, α, α, β] : Fin 5 → ℝ) 3 = α := rfl
    have e4 : (![β, 0, α, α, β] : Fin 5 → ℝ) 4 = β := rfl
    simp only [dotProduct, Fin.sum_univ_five, e0, e1, e2, e3, e4]
    nlinarith [sq_nonneg β, hαpos]

/-- **Target 3.** `gap (a t) → 0` as `t → ∞`. -/
theorem gap_tendsto_zero : Tendsto (fun t : ℕ => gap (avec t)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ Qa_tendsto_Qmin
  · filter_upwards [eventually_ge_atTop 1] with t ht using gap_nonneg (avec_pos ht)
  · filter_upwards [eventually_ge_atTop 1] with t ht using gap_avec_le t ht

/-- For the family `b t` the gap is at least `1` minus two explicit error terms. -/
theorem le_gap_bvec (t : ℕ) (ht : 1 ≤ t) :
    1 - (∑ i, (zmax i - cb t * perron (bvec t) i) ^ 2) - nrm1 (Q (bvec t) - Qmax)
      ≤ gap (bvec t) :=
  le_gap_of_approx (bvec_pos ht) zmax zmax' (cb t) Qmax_form

/-- **Target 5.** `gap (b t) → 1` as `t → ∞`. -/
theorem gap_tendsto_one : Tendsto (fun t : ℕ => gap (bvec t)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun t : ℕ =>
      1 - (∑ i, (zmax i - cb t * perron (bvec t) i) ^ 2) - nrm1 (Q (bvec t) - Qmax))
      atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub
      perron_b_approx_tendsto).sub Qb_tendsto_Qmax
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with t ht using le_gap_bvec t ht
  · filter_upwards [eventually_ge_atTop 1] with t ht using (gap_lt_one (bvec_pos ht)).le

end Brockian.UnbalancedPentagon

import Brockian.Gap

/-!
# Elementary Weyl-type perturbation bounds for real symmetric `5 × 5` matrices

All the eigenvalue continuity we need is packaged in two statements.

* `gap_le_nrm1_of_eigen`: if `B` fixes a vector `v` orthogonal to the Perron vector of `m`,
  then `gap m ≤ ‖Q m - B‖₁` (entrywise `ℓ¹` norm).  This is a Weyl upper bound for the gap.
* `le_gap_of_approx`: if the quadratic form of `B` is dominated by `(z ⬝ x)²` and the Perron
  direction of `m` is close to `z`, then `gap m` is close to `1`.

The entrywise `ℓ¹` norm `nrm1` dominates the `ℓ²` operator norm (see `Brockian.OpNorm`).
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

lemma nrm1_nonneg (A : Matrix (Fin 5) (Fin 5) ℝ) : 0 ≤ nrm1 A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma dotProduct_self_eq_sum_sq (v : Fin 5 → ℝ) : v ⬝ᵥ v = ∑ k, (v k) ^ 2 := by
  simp [dotProduct, sq]

lemma sq_le_dot_self (v : Fin 5 → ℝ) (i : Fin 5) : (v i) ^ 2 ≤ v ⬝ᵥ v := by
  rw [dotProduct_self_eq_sum_sq]
  exact Finset.single_le_sum (f := fun k => (v k) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)

/-- The Rayleigh form is controlled by the entrywise `ℓ¹` norm. -/
lemma abs_dot_mulVec_le (A : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ nrm1 A * (v ⬝ᵥ v) := by
  rw [dot_mulVec, nrm1, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  have hij : |v i| * |v j| ≤ v ⬝ᵥ v := by
    have h1 := sq_le_dot_self v i
    have h2 := sq_le_dot_self v j
    nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
  calc |A i j * v i * v j| = |A i j| * (|v i| * |v j|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |A i j| * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_left hij (abs_nonneg _)

/-- **Weyl upper bound.**  If `B` fixes a nonzero vector orthogonal to the Perron vector of
`Q m`, then the gap is at most the entrywise distance from `Q m` to `B`. -/
theorem gap_le_nrm1_of_eigen (hm : ∀ i, 0 < m i) {B : Matrix (Fin 5) (Fin 5) ℝ} {v : Fin 5 → ℝ}
    (hv : perron m ⬝ᵥ v = 0) (hpos : 0 < v ⬝ᵥ v) (hB : B *ᵥ v = v) :
    gap m ≤ nrm1 (Q m - B) := by
  have h1 := le_sec_of_vec hm hv hpos
  have h2 : v ⬝ᵥ (Q m *ᵥ v) = v ⬝ᵥ v + v ⬝ᵥ ((Q m - B) *ᵥ v) := by
    rw [sub_mulVec, dotProduct_sub, hB]; ring
  have h3 := abs_le.mp (abs_dot_mulVec_le (Q m - B) v)
  have h4 : (1 - nrm1 (Q m - B)) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Q m *ᵥ v) := by
    rw [h2]; nlinarith [h3.1]
  have h5 : 1 - nrm1 (Q m - B) ≤ (v ⬝ᵥ (Q m *ᵥ v)) / (v ⬝ᵥ v) := (le_div_iff₀ hpos).mpr h4
  rw [gap]; linarith

/-- **Weyl lower bound.**  If the quadratic form of `B` splits as `(z ⬝ x)² - (z' ⬝ x)²` and the
Perron direction of `Q m` is `ℓ²`-close to `z` (after scaling by `c`), then `gap m` is close
to `1`. -/
theorem le_gap_of_approx (hm : ∀ i, 0 < m i) {B : Matrix (Fin 5) (Fin 5) ℝ} (z z' : Fin 5 → ℝ)
    (c : ℝ) (hB : ∀ x : Fin 5 → ℝ, x ⬝ᵥ (B *ᵥ x) = (z ⬝ᵥ x) ^ 2 - (z' ⬝ᵥ x) ^ 2) :
    1 - (∑ i, (z i - c * perron m i) ^ 2) - nrm1 (Q m - B) ≤ gap m := by
  have hsec : sec (Q m) (perron m) ≤ (∑ i, (z i - c * perron m i) ^ 2) + nrm1 (Q m - B) := by
    refine sec_le_of hm ?_
    intro x hx hp
    have e1 : x ⬝ᵥ (Q m *ᵥ x) = x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ ((Q m - B) *ᵥ x) := by
      rw [sub_mulVec, dotProduct_sub]; ring
    have e2 : x ⬝ᵥ (B *ᵥ x) ≤ (z ⬝ᵥ x) ^ 2 := by
      rw [hB x]; nlinarith [sq_nonneg (z' ⬝ᵥ x)]
    have hzx : z ⬝ᵥ x = (fun i => z i - c * perron m i) ⬝ᵥ x := by
      simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
      have : ∑ i, c * perron m i * x i = c * (perron m ⬝ᵥ x) := by
        rw [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hp, mul_zero, sub_zero]
    have e3 : (z ⬝ᵥ x) ^ 2 ≤ ∑ i, (z i - c * perron m i) ^ 2 := by
      rw [hzx]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => z i - c * perron m i) (fun i => x i)
      have hxx : ∑ i, (x i) ^ 2 = 1 := by rw [← dotProduct_self_eq_sum_sq]; exact hx
      rw [hxx, mul_one] at hcs
      simpa [dotProduct] using hcs
    have e4 := abs_le.mp (abs_dot_mulVec_le (Q m - B) x)
    have e5 : x ⬝ᵥ ((Q m - B) *ᵥ x) ≤ nrm1 (Q m - B) := by
      have := e4.2; rw [hx, mul_one] at this; exact this
    linarith
  rw [gap]; linarith

end Brockian.UnbalancedPentagon

import Brockian.MinMax
import Brockian.OpNorm
import Brockian.Spectrum
import Brockian.Range

/-!
# Unbalanced pentagon gap extremals — main module

This module is the entry point of the development.  For positive fibre sizes
`m : Fin 5 → ℝ` on the vertices of the 5-cycle we work with

* `deg m i = m (i-1) + m (i+1)`,
* `Q m i j = √(m i * m j / (deg m i * deg m j))` on the edges of `C₅` and `0` elsewhere,
* `perron m i = √(m i * deg m i)`, which satisfies `Q m *ᵥ perron m = perron m`
  (`Q_mulVec_perron`),
* `gap m = 1 - sec (Q m) (perron m)` where `sec A v` is the supremum of the Rayleigh
  quotient `x ⬝ᵥ (A *ᵥ x)` over unit vectors `x` orthogonal to `v`.

The definition of the gap is *not* vacuous: `gap_eq_one_sub_eigenvalues₀_one` proves

`gap m = 1 - (Q m).eigenvalues₀ 1`,

i.e. the Rayleigh definition on the orthogonal complement of the Perron vector really is
`1` minus the second largest eigenvalue of `Q m`, equivalently the smallest positive
eigenvalue of the normalized Laplacian `1 - Q m`.

## Proved results

1. `gap_lower_bound_of_ratio` : `g5 / rho m ^ 2 ≤ gap m` with `g5 = (5 - √5)/4` and
   `rho m = max m / min m` (weighted Poincaré comparison, `Brockian/LowerBound.lean`,
   with the `C₅` Poincaré constant proved by an explicit SOS certificate in
   `Brockian/Poincare.lean`).
2. `Qa_tendsto_Qmin_opNorm` : `‖Q (avec t) - Qmin‖ → 0`, where `avec t = (t², 1, t², t, t)`
   and `Qmin` carries the edges `{2,3}` and `{4,0}` with weight `1`;
   `Qmin_eigenvalues` : the ordered spectrum of `Qmin` is `1, 1, 0, -1, -1`.
3. `gap_tendsto_zero` : `gap (avec t) → 0`.
4. `Qb_tendsto_Qmax_opNorm` : `‖Q (bvec t) - Qmax‖ → 0`, where `bvec t = (1, 1, t, t², t)`
   and `Qmax` carries the edges `{2,3}` and `{3,4}` with weight `1/√2`;
   `Qmax_eigenvalues` : the ordered spectrum of `Qmax` is `1, 0, 0, 0, -1`.
5. `gap_tendsto_one` : `gap (bvec t) → 1`.
6. `gap_lt_one` : `gap m < 1` for every strictly positive `m`.
7. `gap_sharp_range` : `sInf gapSet = 0`, `sSup gapSet = 1`, and neither endpoint is
   attained, where `gapSet` collects the gaps of positive *integral* fibre sizes.

The eigenvalue continuity used in 3 and 5 is elementary and proved in the project:
`gap_le_nrm1_of_eigen` and `le_gap_of_approx` in `Brockian/Perturb.lean`, together with
`opNorm_le_nrm1` in `Brockian/OpNorm.lean`, which shows that the entrywise `ℓ¹` norm used
there dominates the `ℓ²` operator norm.

## Conjectural improvements (not proved here)

The following statements are *not* part of the formal development; they are recorded only as
informal remarks and no Lean declaration below depends on them.

* The exponent `2` in `g5 / rho m ^ 2 ≤ gap m` is presumably not optimal; numerically a bound
  of the shape `c / rho m` appears to hold for the 5-cycle.
* The convergence rates for the two extremal families appear to be `gap (avec t) = Θ(1/√t)`
  and `1 - gap (bvec t) = Θ(1/√t)`.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Finset Filter Topology
open scoped Matrix.Norms.L2Operator

/-- **The whole package in one statement.**  Each conjunct is one of the required targets;
see the module docstring for the correspondence. -/
theorem unbalanced_pentagon_package :
    (∀ m : Fin 5 → ℝ, (∀ i, 0 < m i) → g5 / rho m ^ 2 ≤ gap m) ∧
    (∀ m : Fin 5 → ℝ, (∀ i, 0 < m i) → gap m = 1 - (Q_isHermitian m).eigenvalues₀ 1) ∧
    Tendsto (fun t : ℕ => ‖Q (avec t) - Qmin‖) atTop (𝓝 0) ∧
    Qmin_isHermitian.eigenvalues₀ = ![1, 1, 0, -1, -1] ∧
    Tendsto (fun t : ℕ => gap (avec t)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℕ => ‖Q (bvec t) - Qmax‖) atTop (𝓝 0) ∧
    Qmax_isHermitian.eigenvalues₀ = ![1, 0, 0, 0, -1] ∧
    Tendsto (fun t : ℕ => gap (bvec t)) atTop (𝓝 1) ∧
    (∀ m : Fin 5 → ℝ, (∀ i, 0 < m i) → gap m < 1) ∧
    (sInf gapSet = 0 ∧ sSup gapSet = 1 ∧ (0:ℝ) ∉ gapSet ∧ (1:ℝ) ∉ gapSet) :=
  ⟨fun _ hm => gap_lower_bound_of_ratio hm,
   fun _ hm => gap_eq_one_sub_eigenvalues₀_one hm,
   Qa_tendsto_Qmin_opNorm,
   Qmin_eigenvalues,
   gap_tendsto_zero,
   Qb_tendsto_Qmax_opNorm,
   Qmax_eigenvalues,
   gap_tendsto_one,
   fun _ hm => gap_lt_one hm,
   gap_sharp_range⟩

end Brockian.UnbalancedPentagon

import Brockian.Fin5

/-!
# Quotient normalized adjacency matrices of an unbalanced pentagon

Let `m : Fin 5 → ℝ` be a vector of (positive) fibre sizes attached to the vertices of the
5-cycle `C₅`.  We set

* `deg m i = m (i-1) + m (i+1)`  (the "combinatorial" degree seen by vertex `i`),
* `wt m i  = m i * deg m i`      (the weighted degree `D i` of vertex `i`),
* `Q m i j = sqrt (m i * m j / (deg m i * deg m j))` on the edges of `C₅`, `0` otherwise.

`Q m` is exactly the normalized adjacency matrix of the weighted 5-cycle whose edge
conductance on `{i, i+1}` is `m i * m (i+1)`: indeed the weighted degree of `i` is
`m i * (m (i-1) + m (i+1)) = wt m i` and
`m i * m j / sqrt (wt m i * wt m j) = sqrt (m i * m j / (deg m i * deg m j))`.

The vector `perron m i = sqrt (wt m i)` is a positive eigenvector of `Q m` for the
eigenvalue `1`; the spectral gap is defined by a Rayleigh quotient on its orthogonal
complement.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix

/-- The degree `d i = m (i-1) + m (i+1)` of vertex `i` in the 5-cycle. -/
def deg (m : Fin 5 → ℝ) (i : Fin 5) : ℝ := m (i - 1) + m (i + 1)

/-- Adjacency relation of the 5-cycle. -/
def Adj (i j : Fin 5) : Prop := j = i + 1 ∨ i = j + 1

instance : DecidableRel Adj := fun i j => inferInstanceAs (Decidable (j = i + 1 ∨ i = j + 1))

/-- The weighted degree `D i = m i * d i` of vertex `i`. -/
def wt (m : Fin 5 → ℝ) (i : Fin 5) : ℝ := m i * deg m i

/-- The symmetric quotient normalized-adjacency matrix. -/
noncomputable def Q (m : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  if Adj i j then Real.sqrt (m i * m j / (deg m i * deg m j)) else 0

/-- The Perron vector `p i = sqrt (m i * d i)`; it satisfies `Q m *ᵥ p = p`. -/
noncomputable def perron (m : Fin 5 → ℝ) (i : Fin 5) : ℝ := Real.sqrt (wt m i)

/-- The set of Rayleigh quotients of `A` at unit vectors orthogonal to `v`. -/
def rayleighSet (A : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℝ) : Set ℝ :=
  {r : ℝ | ∃ x : Fin 5 → ℝ, x ⬝ᵥ x = 1 ∧ v ⬝ᵥ x = 0 ∧ r = x ⬝ᵥ (A *ᵥ x)}

/-- `sec A v` is the supremum of the Rayleigh quotient of `A` over unit vectors orthogonal
to `v`.  When `v` is a unit eigenvector of `A` for its largest eigenvalue this is the
second largest eigenvalue of `A` (see `Brockian.UnbalancedPentagon.sec_eq_eigenvalues₀_one`). -/
noncomputable def sec (A : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℝ) : ℝ :=
  sSup (rayleighSet A v)

/-- The spectral gap: the smallest positive eigenvalue of the normalized Laplacian
`1 - Q m`, defined as `1` minus the second largest eigenvalue of `Q m`. -/
noncomputable def gap (m : Fin 5 → ℝ) : ℝ := 1 - sec (Q m) (perron m)

/-- The Dirichlet energy `∑_{edges} m i * m j * (y i - y j)^2`. -/
def En (m y : Fin 5 → ℝ) : ℝ := ∑ i, m i * m (i + 1) * (y i - y (i + 1)) ^ 2

/-- The weighted mass `∑ i, D i * (y i)^2`. -/
def Ms (m y : Fin 5 → ℝ) : ℝ := ∑ i, wt m i * (y i) ^ 2

/-- The weighted mean condition functional `∑ i, D i * y i`. -/
def Ctr (m y : Fin 5 → ℝ) : ℝ := ∑ i, wt m i * y i

/-- The entrywise `ℓ¹` norm of a matrix; it dominates the `ℓ²` operator norm. -/
def nrm1 (A : Matrix (Fin 5) (Fin 5) ℝ) : ℝ := ∑ i, ∑ j, |A i j|

/-! ### Explicit expansions -/

lemma deg_zero (m : Fin 5 → ℝ) : deg m 0 = m 4 + m 1 := by simp [deg]
lemma deg_one (m : Fin 5 → ℝ) : deg m 1 = m 0 + m 2 := by simp [deg]
lemma deg_two (m : Fin 5 → ℝ) : deg m 2 = m 1 + m 3 := by simp [deg]
lemma deg_three (m : Fin 5 → ℝ) : deg m 3 = m 2 + m 4 := by simp [deg]
lemma deg_four (m : Fin 5 → ℝ) : deg m 4 = m 3 + m 0 := by simp [deg]

lemma deg_pos {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i) (i : Fin 5) : 0 < deg m i := by
  have := hm (i - 1); have := hm (i + 1); simp only [deg]; linarith

lemma wt_pos {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i) (i : Fin 5) : 0 < wt m i :=
  mul_pos (hm i) (deg_pos hm i)

lemma perron_pos {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i) (i : Fin 5) : 0 < perron m i :=
  Real.sqrt_pos.mpr (wt_pos hm i)

lemma perron_sq {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i) (i : Fin 5) :
    perron m i * perron m i = wt m i :=
  Real.mul_self_sqrt (wt_pos hm i).le

lemma En_eq (m y : Fin 5 → ℝ) :
    En m y = m 0 * m 1 * (y 0 - y 1) ^ 2 + m 1 * m 2 * (y 1 - y 2) ^ 2
      + m 2 * m 3 * (y 2 - y 3) ^ 2 + m 3 * m 4 * (y 3 - y 4) ^ 2
      + m 4 * m 0 * (y 4 - y 0) ^ 2 := by
  simp [En, Fin.sum_univ_five]

lemma Ms_eq (m y : Fin 5 → ℝ) :
    Ms m y = wt m 0 * (y 0) ^ 2 + wt m 1 * (y 1) ^ 2 + wt m 2 * (y 2) ^ 2
      + wt m 3 * (y 3) ^ 2 + wt m 4 * (y 4) ^ 2 := by
  simp [Ms, Fin.sum_univ_five]

lemma Ctr_eq (m y : Fin 5 → ℝ) :
    Ctr m y = wt m 0 * y 0 + wt m 1 * y 1 + wt m 2 * y 2 + wt m 3 * y 3 + wt m 4 * y 4 := by
  simp [Ctr, Fin.sum_univ_five]

lemma Q_apply_of_adj {m : Fin 5 → ℝ} {i j : Fin 5} (h : Adj i j) :
    Q m i j = Real.sqrt (m i * m j / (deg m i * deg m j)) := if_pos h

lemma Q_apply_of_not_adj {m : Fin 5 → ℝ} {i j : Fin 5} (h : ¬ Adj i j) : Q m i j = 0 := if_neg h

lemma En_nonneg {m : Fin 5 → ℝ} (hm : ∀ i, 0 ≤ m i) (y : Fin 5 → ℝ) : 0 ≤ En m y := by
  refine Finset.sum_nonneg fun i _ => ?_
  have h1 := hm i; have h2 := hm (i + 1); positivity

end Brockian.UnbalancedPentagon

import Brockian.Gap
import Brockian.Poincare

/-!
# The gap lower bound `g₅ / ρ² ≤ gap`

A weighted Poincaré/Rayleigh comparison against the balanced pentagon.  Edge conductances are
`m i * m j`, vertex weights are `m i * d i`, and the comparison is
`μ² ≤ m i * m j`, `m i * d i ≤ 2 M²` with `μ = min m`, `M = max m`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

/-- The largest fibre size. -/
noncomputable def mmax (m : Fin 5 → ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := Fin 5)) m

/-- The smallest fibre size. -/
noncomputable def mmin (m : Fin 5 → ℝ) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty (α := Fin 5)) m

/-- The unbalancedness ratio `ρ(m) = max m / min m`. -/
noncomputable def rho (m : Fin 5 → ℝ) : ℝ := mmax m / mmin m

lemma le_mmax (m : Fin 5 → ℝ) (i : Fin 5) : m i ≤ mmax m :=
  Finset.le_sup' m (Finset.mem_univ i)

lemma mmin_le (m : Fin 5 → ℝ) (i : Fin 5) : mmin m ≤ m i :=
  Finset.inf'_le m (Finset.mem_univ i)

lemma mmin_pos (hm : ∀ i, 0 < m i) : 0 < mmin m := by
  rw [mmin, Finset.lt_inf'_iff]
  exact fun i _ => hm i

lemma mmax_pos (hm : ∀ i, 0 < m i) : 0 < mmax m := lt_of_lt_of_le (hm 0) (le_mmax m 0)

lemma rho_pos (hm : ∀ i, 0 < m i) : 0 < rho m := div_pos (mmax_pos hm) (mmin_pos hm)

lemma one_le_rho (hm : ∀ i, 0 < m i) : 1 ≤ rho m := by
  rw [rho, le_div_iff₀ (mmin_pos hm), one_mul]
  exact le_trans (mmin_le m 0) (le_mmax m 0)

/-- The core weighted Poincaré inequality: for `y` with zero weighted mean,
`(g₅ μ²/M²) ∑ D i y i² ≤ ∑_{edges} m i m j (y i - y j)²`. -/
theorem weighted_poincare (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ) (hC : Ctr m y = 0) :
    g5 * (mmin m) ^ 2 / (mmax m) ^ 2 * Ms m y ≤ En m y := by
  have hmin := mmin_pos hm
  have hmax := mmax_pos hm
  set c : ℝ := (∑ i, y i) / 5 with hcdef
  set z : Fin 5 → ℝ := fun i => y i - c with hz
  -- (1) `z` is centered
  have h1 : (∑ i, z i) = 0 := by
    simp only [hz, hcdef, Fin.sum_univ_five]
    ring
  -- (2) the energy only depends on differences
  have h2 : En m z = En m y := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hz]; ring
  -- (3) conductance lower bound
  have h3 : (mmin m) ^ 2 * (∑ i, (z i - z (i + 1)) ^ 2) ≤ En m z := by
    rw [En, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have ha : mmin m ≤ m i := mmin_le m i
    have hb : mmin m ≤ m (i + 1) := mmin_le m (i + 1)
    have hmul : (mmin m) ^ 2 ≤ m i * m (i + 1) := by nlinarith
    nlinarith [sq_nonneg (z i - z (i + 1))]
  -- (4) Poincaré on `C₅`
  have h4 : 2 * g5 * (∑ i, (z i) ^ 2) ≤ ∑ i, (z i - z (i + 1)) ^ 2 := c5_poincare_centered h1
  -- (5) weight upper bound
  have h5 : Ms m z ≤ 2 * (mmax m) ^ 2 * (∑ i, (z i) ^ 2) := by
    rw [Ms, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have ha : m i ≤ mmax m := le_mmax m i
    have hb : m (i - 1) ≤ mmax m := le_mmax m (i - 1)
    have hc' : m (i + 1) ≤ mmax m := le_mmax m (i + 1)
    have hmi := hm i
    have hwt : wt m i ≤ 2 * (mmax m) ^ 2 := by
      simp only [wt, deg]; nlinarith
    nlinarith [sq_nonneg (z i)]
  -- (6) centering increases the mass
  have h6 : Ms m y ≤ Ms m z := by
    have hCe : wt m 0 * y 0 + wt m 1 * y 1 + wt m 2 * y 2 + wt m 3 * y 3 + wt m 4 * y 4 = 0 := by
      rw [← Ctr_eq]; exact hC
    have hid : Ms m z = Ms m y
        + c ^ 2 * (wt m 0 + wt m 1 + wt m 2 + wt m 3 + wt m 4) := by
      rw [Ms_eq, Ms_eq]
      simp only [hz]
      linear_combination (-2 * c) * hCe
    have hW : 0 ≤ wt m 0 + wt m 1 + wt m 2 + wt m 3 + wt m 4 := by
      have := wt_pos hm 0; have := wt_pos hm 1; have := wt_pos hm 2
      have := wt_pos hm 3; have := wt_pos hm 4
      linarith
    nlinarith [sq_nonneg c]
  -- combine
  set A : ℝ := ∑ i, (z i) ^ 2 with hA
  have hEn : 2 * g5 * (mmin m) ^ 2 * A ≤ En m y := by
    have ht := mul_le_mul_of_nonneg_left h4 (sq_nonneg (mmin m))
    linarith [ht, h3, h2]
  have hMs : Ms m y ≤ 2 * (mmax m) ^ 2 * A := le_trans h6 h5
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have t1 := mul_le_mul_of_nonneg_left hMs (mul_nonneg g5_pos.le (sq_nonneg (mmin m)))
  have t2 := mul_le_mul_of_nonneg_left hEn (sq_nonneg (mmax m))
  nlinarith [t1, t2]

/-- **Target 1.** `g₅ / ρ(m)² ≤ gap m` for every positive fibre-size vector. -/
theorem gap_lower_bound_of_ratio (hm : ∀ i, 0 < m i) : g5 / (rho m) ^ 2 ≤ gap m := by
  have hmin := mmin_pos hm
  have hmax := mmax_pos hm
  have hrw : g5 / (rho m) ^ 2 = g5 * (mmin m) ^ 2 / (mmax m) ^ 2 := by
    rw [rho, div_pow, div_div_eq_mul_div]
  rw [hrw]
  exact le_gap_of_poincare hm fun y hC => weighted_poincare hm y hC

end Brockian.UnbalancedPentagon

import Brockian.FamilyDefs

/-!
# Entrywise limits for the family `a t = (t², 1, t², t, t)`

With `d = (t+1, 2t², 1+t, t²+t, t+t²)` the nonzero entries of `Q (a t)` are, for `t ≥ 1`,

* `Q (a t) 0 1 = Q (a t) 1 0 = √(1/(2(t+1)))`,
* `Q (a t) 1 2 = Q (a t) 2 1 = √(1/(2(t+1)))`,
* `Q (a t) 2 3 = Q (a t) 3 2 = t/(t+1)`,
* `Q (a t) 3 4 = Q (a t) 4 3 = 1/(t+1)`,
* `Q (a t) 4 0 = Q (a t) 0 4 = t/(t+1)`,

so `Q (a t) → Qmin` entrywise, with error `O(1/√t)`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

section Entries

variable {t : ℕ}

private lemma tpos (ht : 1 ≤ t) : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht

lemma Qa_01_eq (ht : 1 ≤ t) :
    Q (avec t) 0 1 = Real.sqrt ((t : ℝ)⁻¹ / (2 * (1 + (t : ℝ)⁻¹))) := by
  have h := tpos ht
  obtain ⟨d0, d1, _, _, _⟩ := deg_avec t
  rw [Q_apply_of_adj (by decide : Adj (0 : Fin 5) 1), d0, d1]
  congr 1
  simp only [avec_zero, avec_one]
  field_simp

lemma Qa_12_eq (ht : 1 ≤ t) :
    Q (avec t) 1 2 = Real.sqrt ((t : ℝ)⁻¹ / (2 * (1 + (t : ℝ)⁻¹))) := by
  have h := tpos ht
  obtain ⟨_, d1, d2, _, _⟩ := deg_avec t
  rw [Q_apply_of_adj (by decide : Adj (1 : Fin 5) 2), d1, d2]
  congr 1
  simp only [avec_one, avec_two]
  field_simp
  ring

lemma Qa_23_eq (ht : 1 ≤ t) :
    Q (avec t) 2 3 = Real.sqrt (1 / (1 + (t : ℝ)⁻¹) ^ 2) := by
  have h := tpos ht
  obtain ⟨_, _, d2, d3, _⟩ := deg_avec t
  rw [Q_apply_of_adj (by decide : Adj (2 : Fin 5) 3), d2, d3]
  congr 1
  simp only [avec_two, avec_three]
  field_simp
  ring

lemma Qa_34_eq (ht : 1 ≤ t) :
    Q (avec t) 3 4 = Real.sqrt ((t : ℝ)⁻¹ ^ 2 / (1 + (t : ℝ)⁻¹) ^ 2) := by
  have h := tpos ht
  obtain ⟨_, _, _, d3, d4⟩ := deg_avec t
  rw [Q_apply_of_adj (by decide : Adj (3 : Fin 5) 4), d3, d4]
  congr 1
  simp only [avec_three, avec_four]
  field_simp
  ring

lemma Qa_40_eq (ht : 1 ≤ t) :
    Q (avec t) 4 0 = Real.sqrt (1 / (1 + (t : ℝ)⁻¹) ^ 2) := by
  have h := tpos ht
  obtain ⟨d0, _, _, _, d4⟩ := deg_avec t
  rw [Q_apply_of_adj (by decide : Adj (4 : Fin 5) 0), d4, d0]
  congr 1
  simp only [avec_four, avec_zero]
  field_simp
  ring

end Entries

/-! ### Continuity of the profile functions -/

lemma contAt_prof1 : ContinuousAt (fun u : ℝ => Real.sqrt (u / (2 * (1 + u)))) 0 := by
  have h : ContinuousAt (fun u : ℝ => u / (2 * (1 + u))) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  exact Real.continuous_sqrt.continuousAt.comp h

lemma contAt_prof2 : ContinuousAt (fun u : ℝ => Real.sqrt (1 / (1 + u) ^ 2)) 0 := by
  have h : ContinuousAt (fun u : ℝ => 1 / (1 + u) ^ 2) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  exact Real.continuous_sqrt.continuousAt.comp h

lemma contAt_prof3 : ContinuousAt (fun u : ℝ => Real.sqrt (u ^ 2 / (1 + u) ^ 2)) 0 := by
  have h : ContinuousAt (fun u : ℝ => u ^ 2 / (1 + u) ^ 2) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  exact Real.continuous_sqrt.continuousAt.comp h

/-! ### Entrywise limits -/

lemma Qa_01_tendsto : Tendsto (fun t : ℕ => Q (avec t) 0 1) atTop (𝓝 0) :=
  tendsto_of_eq_at_inv' contAt_prof1 (by norm_num) fun _ ht => Qa_01_eq ht

lemma Qa_12_tendsto : Tendsto (fun t : ℕ => Q (avec t) 1 2) atTop (𝓝 0) :=
  tendsto_of_eq_at_inv' contAt_prof1 (by norm_num) fun _ ht => Qa_12_eq ht

lemma Qa_23_tendsto : Tendsto (fun t : ℕ => Q (avec t) 2 3) atTop (𝓝 1) :=
  tendsto_of_eq_at_inv' contAt_prof2 (by norm_num) fun _ ht => Qa_23_eq ht

lemma Qa_34_tendsto : Tendsto (fun t : ℕ => Q (avec t) 3 4) atTop (𝓝 0) :=
  tendsto_of_eq_at_inv' contAt_prof3 (by norm_num) fun _ ht => Qa_34_eq ht

lemma Qa_40_tendsto : Tendsto (fun t : ℕ => Q (avec t) 4 0) atTop (𝓝 1) :=
  tendsto_of_eq_at_inv' contAt_prof2 (by norm_num) fun _ ht => Qa_40_eq ht

lemma Qa_10_tendsto : Tendsto (fun t : ℕ => Q (avec t) 1 0) atTop (𝓝 0) := by
  have h : (fun t : ℕ => Q (avec t) 1 0) = fun t : ℕ => Q (avec t) 0 1 :=
    funext fun t => Q_symm _ 1 0
  rw [h]; exact Qa_01_tendsto

lemma Qa_21_tendsto : Tendsto (fun t : ℕ => Q (avec t) 2 1) atTop (𝓝 0) := by
  have h : (fun t : ℕ => Q (avec t) 2 1) = fun t : ℕ => Q (avec t) 1 2 :=
    funext fun t => Q_symm _ 2 1
  rw [h]; exact Qa_12_tendsto

lemma Qa_32_tendsto : Tendsto (fun t : ℕ => Q (avec t) 3 2) atTop (𝓝 1) := by
  have h : (fun t : ℕ => Q (avec t) 3 2) = fun t : ℕ => Q (avec t) 2 3 :=
    funext fun t => Q_symm _ 3 2
  rw [h]; exact Qa_23_tendsto

lemma Qa_43_tendsto : Tendsto (fun t : ℕ => Q (avec t) 4 3) atTop (𝓝 0) := by
  have h : (fun t : ℕ => Q (avec t) 4 3) = fun t : ℕ => Q (avec t) 3 4 :=
    funext fun t => Q_symm _ 4 3
  rw [h]; exact Qa_34_tendsto

lemma Qa_04_tendsto : Tendsto (fun t : ℕ => Q (avec t) 0 4) atTop (𝓝 1) := by
  have h : (fun t : ℕ => Q (avec t) 0 4) = fun t : ℕ => Q (avec t) 4 0 :=
    funext fun t => Q_symm _ 0 4
  rw [h]; exact Qa_40_tendsto

/-- Off the 5-cycle both matrices vanish. -/
lemma Qa_zero_entry {i j : Fin 5} (h : ¬ Adj i j) (h2 : Qmin i j = 0) :
    Tendsto (fun t : ℕ => Q (avec t) i j) atTop (𝓝 (Qmin i j)) := by
  simp only [Q_apply_of_not_adj h, h2]
  exact tendsto_const_nhds

/-- Entrywise convergence `Q (a t) → Qmin`. -/
theorem Qa_entry_tendsto (i j : Fin 5) :
    Tendsto (fun t : ℕ => Q (avec t) i j) atTop (𝓝 (Qmin i j)) := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact Qa_zero_entry (by decide) rfl
      | exact Qa_01_tendsto
      | exact Qa_10_tendsto
      | exact Qa_12_tendsto
      | exact Qa_21_tendsto
      | exact Qa_23_tendsto
      | exact Qa_32_tendsto
      | exact Qa_34_tendsto
      | exact Qa_43_tendsto
      | exact Qa_40_tendsto
      | exact Qa_04_tendsto

/-- **Target 2 (convergence).** `Q (a t) → Qmin` in the entrywise `ℓ¹` norm, hence in every
matrix norm. -/
theorem Qa_tendsto_Qmin : Tendsto (fun t : ℕ => nrm1 (Q (avec t) - Qmin)) atTop (𝓝 0) :=
  nrm1_tendsto_zero Qa_entry_tendsto

end Brockian.UnbalancedPentagon

import Mathlib

/-!
# Cyclic index arithmetic on `Fin 5`

Small helper simp lemmas so that all sums/expressions indexed by the vertices of the
5-cycle can be expanded into explicit five-term formulas.
-/

namespace Brockian.Fin5

@[simp] lemma add_one_0 : (0 : Fin 5) + 1 = 1 := rfl
@[simp] lemma add_one_1 : (1 : Fin 5) + 1 = 2 := rfl
@[simp] lemma add_one_2 : (2 : Fin 5) + 1 = 3 := rfl
@[simp] lemma add_one_3 : (3 : Fin 5) + 1 = 4 := rfl
@[simp] lemma add_one_4 : (4 : Fin 5) + 1 = 0 := rfl

@[simp] lemma neg_one : (-1 : Fin 5) = 4 := rfl

@[simp] lemma sub_one_0 : (0 : Fin 5) - 1 = 4 := rfl
@[simp] lemma sub_one_1 : (1 : Fin 5) - 1 = 0 := rfl
@[simp] lemma sub_one_2 : (2 : Fin 5) - 1 = 1 := rfl
@[simp] lemma sub_one_3 : (3 : Fin 5) - 1 = 2 := rfl
@[simp] lemma sub_one_4 : (4 : Fin 5) - 1 = 3 := rfl

end Brockian.Fin5

import Brockian.GapLimits

/-!
# The sharp range of the spectral gap over positive integral fibre sizes

`gapSet` is the set of all values `gap m` for strictly positive integral fibre-size vectors
`m : Fin 5 → ℕ`.  We show `sInf gapSet = 0`, `sSup gapSet = 1`, and that neither endpoint is
attained: every value lies strictly between `0` and `1`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

/-- The gap is strictly positive for any positive fibre-size vector. -/
theorem gap_pos {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i) : 0 < gap m :=
  lt_of_lt_of_le (div_pos g5_pos (pow_pos (rho_pos hm) 2)) (gap_lower_bound_of_ratio hm)

/-- The set of spectral gaps of positive integral fibre-size vectors. -/
def gapSet : Set ℝ := {r : ℝ | ∃ m : Fin 5 → ℕ, (∀ i, 0 < m i) ∧ r = gap (fun i => (m i : ℝ))}

lemma gapSet_subset_Ioo : gapSet ⊆ Set.Ioo (0:ℝ) 1 := by
  rintro r ⟨m, hm, rfl⟩
  have hpos : ∀ i, (0:ℝ) < (m i : ℝ) := fun i => by exact_mod_cast hm i
  exact ⟨gap_pos hpos, gap_lt_one hpos⟩

lemma gapSet_nonempty : gapSet.Nonempty :=
  ⟨gap (fun _ => (1:ℝ)), ⟨fun _ => 1, fun _ => Nat.one_pos, by norm_num⟩⟩

lemma gapSet_bddBelow : BddBelow gapSet := ⟨0, fun _ hr => (gapSet_subset_Ioo hr).1.le⟩

lemma gapSet_bddAbove : BddAbove gapSet := ⟨1, fun _ hr => (gapSet_subset_Ioo hr).2.le⟩

lemma mem_gapSet_avec {t : ℕ} (ht : 1 ≤ t) : gap (avec t) ∈ gapSet :=
  ⟨aN t, aN_pos ht, rfl⟩

lemma mem_gapSet_bvec {t : ℕ} (ht : 1 ≤ t) : gap (bvec t) ∈ gapSet :=
  ⟨bN t, bN_pos ht, rfl⟩

/-- **Target 7 (infimum).** The infimum of the spectral gap over positive integral fibre
sizes is `0`. -/
theorem sInf_gapSet : sInf gapSet = 0 := by
  refine le_antisymm ?_ ?_
  · refine ge_of_tendsto gap_tendsto_zero ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact csInf_le gapSet_bddBelow (mem_gapSet_avec ht)
  · exact le_csInf gapSet_nonempty fun _ hr => (gapSet_subset_Ioo hr).1.le

/-- **Target 7 (supremum).** The supremum of the spectral gap over positive integral fibre
sizes is `1`. -/
theorem sSup_gapSet : sSup gapSet = 1 := by
  refine le_antisymm ?_ ?_
  · exact csSup_le gapSet_nonempty fun _ hr => (gapSet_subset_Ioo hr).2.le
  · refine le_of_tendsto gap_tendsto_one ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact le_csSup gapSet_bddAbove (mem_gapSet_bvec ht)

/-- The infimum is not attained. -/
theorem zero_notMem_gapSet : (0:ℝ) ∉ gapSet := fun h => lt_irrefl 0 (gapSet_subset_Ioo h).1

/-- The supremum is not attained. -/
theorem one_notMem_gapSet : (1:ℝ) ∉ gapSet := fun h => lt_irrefl 1 (gapSet_subset_Ioo h).2

/-- **Target 7.** Sharp range: the gap ranges over a subset of `(0,1)` with infimum `0` and
supremum `1`, neither of which is attained. -/
theorem gap_sharp_range :
    sInf gapSet = 0 ∧ sSup gapSet = 1 ∧ (0:ℝ) ∉ gapSet ∧ (1:ℝ) ∉ gapSet :=
  ⟨sInf_gapSet, sSup_gapSet, zero_notMem_gapSet, one_notMem_gapSet⟩

end Brockian.UnbalancedPentagon

import Brockian.Gap

/-!
# `gap m < 1` for every positive fibre-size vector

Take the test function `y = (1, 1, 0, τ, 0)` with `τ = -(D 0 + D 1)/D 3`, which has zero
weighted mean.  Its Dirichlet energy is `Ms m y - 2 m 0 m 1`, strictly smaller than its mass,
because the edge `{0,1}` carries no oscillation.  This is the variational counterpart of the
fact that a positive weighted 5-cycle has a positive second adjacency eigenvalue.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

/-- **Target 6.** The spectral gap of a positive unbalanced pentagon is `< 1`. -/
theorem gap_lt_one (hm : ∀ i, 0 < m i) : gap m < 1 := by
  have w0 := wt_pos hm 0
  have w1 := wt_pos hm 1
  have w2 := wt_pos hm 2
  have w3 := wt_pos hm 3
  have w4 := wt_pos hm 4
  set τ : ℝ := -(wt m 0 + wt m 1) / wt m 3 with hτ
  set y : Fin 5 → ℝ := ![1, 1, 0, τ, 0] with hy
  have hy0 : y 0 = 1 := rfl
  have hy1 : y 1 = 1 := rfl
  have hy2 : y 2 = 0 := rfl
  have hy3 : y 3 = τ := rfl
  have hy4 : y 4 = 0 := rfl
  have hC : Ctr m y = 0 := by
    rw [Ctr_eq, hy0, hy1, hy2, hy3, hy4, hτ]
    have h3 : wt m 3 ≠ 0 := ne_of_gt w3
    field_simp
    ring
  have hM : 0 < Ms m y := by
    rw [Ms_eq, hy0, hy1, hy2, hy3, hy4]
    have : 0 ≤ wt m 3 * τ ^ 2 := by positivity
    nlinarith
  have hE : En m y = Ms m y - 2 * (m 0 * m 1) := by
    rw [En_eq, Ms_eq, hy0, hy1, hy2, hy3, hy4]
    simp only [wt, deg_zero, deg_one, deg_two, deg_three, deg_four]
    ring
  have hle := gap_le_of_test hm y hC hM
  rw [hE] at hle
  have hlt : (Ms m y - 2 * (m 0 * m 1)) / Ms m y < 1 := by
    rw [div_lt_one hM]
    have := mul_pos (hm 0) (hm 1)
    linarith
  linarith

end Brockian.UnbalancedPentagon

import Brockian.LimitMatrices

/-!
# Ordered eigenvalues of the two limiting matrices

We compute the characteristic polynomials of `Qmin` and `Qmax` explicitly and deduce their
ordered eigenvalue lists:

* `Qmin` has spectrum `1, 1, 0, -1, -1`;
* `Qmax` has spectrum `1, 0, 0, 0, -1`.

The bridge from a factored characteristic polynomial to Mathlib's ordered eigenvalues
`Matrix.IsHermitian.eigenvalues₀` is `eigenvalues₀_eq_of_charpoly`.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Polynomial

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- If the characteristic polynomial of a real symmetric `5 × 5` matrix factors with the
antitone root list `μ`, then `μ` is exactly the list of ordered eigenvalues. -/
theorem eigenvalues₀_eq_of_charpoly (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.IsHermitian)
    (μ : Fin 5 → ℝ) (hμ : Antitone μ)
    (hc : A.charpoly = ∏ i, (X - C (μ i))) : hA.eigenvalues₀ = μ := by
  have hroots : A.charpoly.roots = Multiset.map μ Finset.univ.val := by
    rw [hc, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  have h2 : (Multiset.map (RCLike.re : ℝ → ℝ) (Multiset.map μ Finset.univ.val)).sort (· ≥ ·)
      = List.ofFn μ := by
    rw [Multiset.map_map]
    simp only [Function.comp_def, RCLike.re_to_real]
    rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn
  rw [h2] at hsort
  exact List.ofFn_injective hsort.symm

/-! ### `Qmin` -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- The characteristic polynomial of `Qmin` is `(X-1)²X(X+1)²`. -/
theorem Qmin_charpoly : Qmin.charpoly = ∏ i : Fin 5, (X - C (![1, 1, 0, -1, -1] i : ℝ)) := by
  simp [Matrix.charpoly, Matrix.charmatrix, Qmin, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.prod_univ_five, Fin.succAbove]
  ring

lemma Qmin_isHermitian : Qmin.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qmin]

theorem Qmin_eigenvalues : Qmin_isHermitian.eigenvalues₀ = ![1, 1, 0, -1, -1] := by
  refine eigenvalues₀_eq_of_charpoly _ _ _ ?_ Qmin_charpoly
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-! ### `Qmax` -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- The characteristic polynomial of `Qmax` is `(X-1)X³(X+1)`. -/
theorem Qmax_charpoly : Qmax.charpoly = ∏ i : Fin 5, (X - C (![1, 0, 0, 0, -1] i : ℝ)) := by
  have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [h]
  have hC : (C (1 / 2 : ℝ)) * 2 = 1 := by
    rw [show (2 : Polynomial ℝ) = C (2 : ℝ) from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  simp [Matrix.charpoly, Matrix.charmatrix, Qmax, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.prod_univ_five, Fin.succAbove]
  have h2' : (C (Real.sqrt 2 * (1 / 2)) : Polynomial ℝ) ^ 2 = C (1 / 2 : ℝ) := by
    rw [← C_pow]
    congr 1
    nlinarith [h2]
  ring_nf
  linear_combination (-2 * (X : Polynomial ℝ) ^ 3) * h2' + (-(X : Polynomial ℝ) ^ 3) * hC

lemma Qmax_isHermitian : Qmax.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qmax]

theorem Qmax_eigenvalues : Qmax_isHermitian.eigenvalues₀ = ![1, 0, 0, 0, -1] := by
  refine eigenvalues₀_eq_of_charpoly _ _ _ ?_ Qmax_charpoly
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end Brockian.UnbalancedPentagon

