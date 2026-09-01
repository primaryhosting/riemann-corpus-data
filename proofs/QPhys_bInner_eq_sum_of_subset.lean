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
# A model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are not vacuous:
we build an explicit complex inner product space (the polynomials `ℂ[X]` with the
Bargmann–Fock inner product `⟪p, q⟫ = ∑ n ! * conj (pₙ) * qₙ`), two symmetric operators
`Xop`, `Pop` on it satisfying `[Xop, Pop] = 2 i`, and a normalized state.
-/

import Mathlib
import RequestProject.HeisenbergUncertainty

/-!
# A model for the canonical commutation relation (Bargmann–Fock space of polynomials)
-/

namespace QPhys

open Polynomial ComplexConjugate

/-- The Bargmann–Fock inner product on polynomials: `⟪p, q⟫ = ∑ₙ n! * conj pₙ * qₙ`. -/
noncomputable def bInner (p q : ℂ[X]) : ℂ :=
  ∑ n ∈ p.support, (Nat.factorial n : ℂ) * conj (p.coeff n) * q.coeff n

lemma bInner_eq_sum_of_subset {p : ℂ[X]} {s : Finset ℕ} (hs : p.support ⊆ s) (q : ℂ[X]) :
    bInner p q = ∑ n ∈ s, (Nat.factorial n : ℂ) * conj (p.coeff n) * q.coeff n := by
  refine Finset.sum_subset hs fun n _ hn => ?_
  have : p.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
  simp [this]

lemma bInner_conj_symm (p q : ℂ[X]) : conj (bInner q p) = bInner p q := by
  rw [bInner_eq_sum_of_subset (Finset.subset_union_right (s₁ := p.support)) p,
      bInner_eq_sum_of_subset (Finset.subset_union_left (s₂ := q.support)) q, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [map_mul, Complex.conj_conj, Complex.conj_natCast]
  ring

lemma bInner_add_left (p q r : ℂ[X]) : bInner (p + q) r = bInner p r + bInner q r := by
  rw [bInner_eq_sum_of_subset (Polynomial.support_add (p := p) (q := q)) r,
      bInner_eq_sum_of_subset (Finset.subset_union_left (s₂ := q.support)) r,
      bInner_eq_sum_of_subset (Finset.subset_union_right (s₁ := p.support)) r,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Polynomial.coeff_add, map_add]
  ring

lemma bInner_smul_left (p q : ℂ[X]) (c : ℂ) : bInner (c • p) q = conj c * bInner p q := by
  rw [bInner_eq_sum_of_subset (Polynomial.support_smul c p) q,
      bInner_eq_sum_of_subset (le_refl p.support) q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Polynomial.coeff_smul, smul_eq_mul, map_mul]
  ring

lemma bInner_self_re (p : ℂ[X]) :
    (bInner p p).re = ∑ n ∈ p.support, (Nat.factorial n : ℝ) * Complex.normSq (p.coeff n) := by
  rw [bInner, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma bInner_self_nonneg (p : ℂ[X]) : 0 ≤ (bInner p p).re := by
  rw [bInner_self_re]
  exact Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

lemma bInner_definite (p : ℂ[X]) (h : bInner p p = 0) : p = 0 := by
  have hre : ∑ n ∈ p.support, (Nat.factorial n : ℝ) * Complex.normSq (p.coeff n) = 0 := by
    rw [← bInner_self_re, h, Complex.zero_re]
  have hz : ∀ n ∈ p.support, (Nat.factorial n : ℝ) * Complex.normSq (p.coeff n) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun n _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))).mp hre
  ext n
  by_cases hn : n ∈ p.support
  · have hzn := hz n hn
    have hf : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hnorm : Complex.normSq (p.coeff n) = 0 := by
      rcases mul_eq_zero.mp hzn with h1 | h2
      · exact absurd h1 hf
      · exact h2
    simpa using Complex.normSq_eq_zero.mp hnorm
  · simpa using Polynomial.notMem_support_iff.mp hn

/-- The Bargmann–Fock inner product turns `ℂ[X]` into an inner product space. -/
noncomputable def bargmannCore : InnerProductSpace.Core ℂ ℂ[X] where
  inner := bInner
  conj_inner_symm := bInner_conj_symm
  re_inner_nonneg := bInner_self_nonneg
  add_left := bInner_add_left
  smul_left := bInner_smul_left
  definite := bInner_definite

noncomputable abbrev bargmannNACG : NormedAddCommGroup ℂ[X] :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ ℂ[X] _ _ _ bargmannCore

attribute [local instance] bargmannNACG

noncomputable instance bargmannIPS : InnerProductSpace ℂ ℂ[X] :=
  InnerProductSpace.ofCore bargmannCore.toCore

lemma inner_eq_bInner (p q : ℂ[X]) : (inner ℂ p q : ℂ) = bInner p q := rfl

/-- Multiplication by `X` (the creation operator) is adjoint to differentiation
(the annihilation operator). -/
lemma bInner_X_mul_left (p q : ℂ[X]) : bInner (X * p) q = bInner p (derivative q) := by
  set M := p.natDegree + 1 with hM
  have h1 : (X * p).support ⊆ Finset.range (M + 1) := by
    refine Polynomial.supp_subset_range ?_
    have := Polynomial.natDegree_mul_le (p := (X : ℂ[X])) (q := p)
    simp [Polynomial.natDegree_X] at this
    omega
  have h2 : p.support ⊆ Finset.range M := Polynomial.supp_subset_range (by omega)
  rw [bInner_eq_sum_of_subset h1 q, bInner_eq_sum_of_subset h2 (derivative q),
      Finset.sum_range_succ']
  simp only [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
  have h0 : (Nat.factorial 0 : ℂ) * conj ((X * p).coeff 0) * q.coeff 0 = 0 := by simp
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hfac : (Nat.factorial (m + 1) : ℂ) = (m + 1) * (Nat.factorial m : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac]
  ring

/-- Differentiation is adjoint to multiplication by `X`. -/
lemma bInner_derivative_left (p q : ℂ[X]) : bInner (derivative p) q = bInner p (X * q) :=
  calc bInner (derivative p) q = conj (bInner q (derivative p)) := (bInner_conj_symm _ _).symm
    _ = conj (bInner (X * q) p) := by rw [bInner_X_mul_left]
    _ = bInner p (X * q) := bInner_conj_symm _ _

/-- The annihilation operator `a = d/dX`. -/
noncomputable def aOp : ℂ[X] →ₗ[ℂ] ℂ[X] := Polynomial.derivative

/-- The creation operator `a† = X ·`. -/
noncomputable def adOp : ℂ[X] →ₗ[ℂ] ℂ[X] := LinearMap.mulLeft ℂ (X : ℂ[X])

/-- Position-like operator `Xop = a + a†`. -/
noncomputable def Xop : ℂ[X] →ₗ[ℂ] ℂ[X] := aOp + adOp

/-- Momentum-like operator `Pop = i (a† - a)`. -/
noncomputable def Pop : ℂ[X] →ₗ[ℂ] ℂ[X] := Complex.I • (adOp - aOp)

lemma aOp_apply (p : ℂ[X]) : aOp p = derivative p := rfl
lemma adOp_apply (p : ℂ[X]) : adOp p = X * p := rfl

lemma Xop_symmetric : IsSymmetricOp Xop := by
  intro u v
  simp only [inner_eq_bInner, Xop, LinearMap.add_apply, aOp_apply, adOp_apply,
    bInner_add_left]
  rw [bInner_X_mul_left, bInner_derivative_left]
  have h1 : bInner u (derivative v + X * v) = bInner u (derivative v) + bInner u (X * v) := by
    simp only [bInner, Polynomial.coeff_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h1]
  ring

lemma Pop_symmetric : IsSymmetricOp Pop := by
  intro u v
  simp only [inner_eq_bInner, Pop, LinearMap.smul_apply, LinearMap.sub_apply, aOp_apply,
    adOp_apply]
  have hl : bInner (Complex.I • (X * u - derivative u)) v
      = conj Complex.I * bInner (X * u - derivative u) v := bInner_smul_left _ _ _
  have hsub : ∀ a b c : ℂ[X], bInner (a - b) c = bInner a c - bInner b c := by
    intro a b c
    have := bInner_add_left (a - b) b c
    rw [sub_add_cancel] at this
    linear_combination -this
  rw [hl, hsub, bInner_X_mul_left, bInner_derivative_left]
  have hr : bInner u (Complex.I • (X * v - derivative v))
      = Complex.I * (bInner u (X * v) - bInner u (derivative v)) := by
    simp only [bInner, Polynomial.coeff_smul, Polynomial.coeff_sub, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hr]
  simp only [Complex.conj_I]
  ring

/-- The canonical commutation relation `[Xop, Pop] = 2 i` holds in this model. -/
lemma ccr_Xop_Pop (u : ℂ[X]) : Xop (Pop u) - Pop (Xop u) = (Complex.I * ((2 : ℝ) : ℂ)) • u := by
  have hd : ∀ v : ℂ[X], derivative (X * v) = v + X * derivative v := by
    intro v
    rw [derivative_mul, derivative_X]
    ring
  simp only [Xop, Pop, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    aOp_apply, adOp_apply, map_smul, map_sub, derivative_add, derivative_mul, derivative_X,
    smul_sub, mul_add, smul_add]
  push_cast
  simp only [Polynomial.smul_eq_C_mul, map_mul, map_ofNat]
  ring

/-- The constant polynomial `1` is a normalized state. -/
lemma norm_one_eq_one : ‖(1 : ℂ[X])‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  show Real.sqrt (bInner 1 1).re = 1
  rw [bInner, ← Polynomial.C_1, Polynomial.support_C one_ne_zero]
  simp

/-- **Non-vacuity of the uncertainty principle.**  In the Bargmann–Fock model, with
`ℏ = 2`, the operators `Xop` and `Pop` are symmetric, satisfy `[Xop, Pop] = 2 i`, and the
state `1` is normalized; hence the uncertainty product is at least `1`. -/
theorem bargmann_uncertainty :
    stdDev Xop (1 : ℂ[X]) * stdDev Pop (1 : ℂ[X]) ≥ (2 : ℝ) / 2 :=
  heisenberg_uncertainty Xop_symmetric Pop_symmetric 2 ccr_Xop_Pop 1 norm_one_eq_one

end QPhys

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator `A` on a complex inner product space is *symmetric* (formally self-adjoint)
if `⟪A u, v⟫ = ⟪u, A v⟫` for all `u, v`. -/
def IsSymmetricOp (A : H →ₗ[ℂ] H) : Prop := ∀ u v : H, inner ℂ (A u) v = inner ℂ u (A v)

/-- The expectation value `⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`.  For a symmetric
operator this complex number is real, and we take its real part. -/
noncomputable def mean (A : H →ₗ[ℂ] H) (psi : H) : ℝ := (inner ℂ psi (A psi) : ℂ).re

/-- The standard deviation (uncertainty) of an operator `A` in the state `ψ`:
`Δ A = ‖(A - ⟪A⟫) ψ‖`.  For a normalized state and symmetric `A` this is the usual
`√(⟪A²⟫ - ⟪A⟫²)`. -/
noncomputable def stdDev (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  ‖A psi - ((mean A psi : ℝ) : ℂ) • psi‖

/-- The expectation value of a symmetric operator is real. -/
lemma mean_coe_eq_inner {A : H →ₗ[ℂ] H} (hA : IsSymmetricOp A) (psi : H) :
    ((mean A psi : ℝ) : ℂ) = inner ℂ psi (A psi) :=
  Complex.conj_eq_iff_re.mp ((inner_conj_symm (A psi) psi).trans (hA psi psi))

/-- The commutator relation transfers to the mean-subtracted vectors: the imaginary part of
`⟪(X - ⟪X⟫)ψ, (P - ⟪P⟫)ψ⟫` equals `ℏ/2`. -/
lemma inner_im_eq {X P : H →ₗ[ℂ] H} (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    (hbar : ℝ) (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    (inner ℂ (X psi - ((mean X psi : ℝ) : ℂ) • psi)
        (P psi - ((mean P psi : ℝ) : ℂ) • psi) : ℂ).im = hbar / 2 := by
  set a : ℂ := ((mean X psi : ℝ) : ℂ) with ha
  set b : ℂ := ((mean P psi : ℝ) : ℂ) with hb
  set z : ℂ := inner ℂ (X psi - a • psi) (P psi - b • psi) with hz
  -- The commutator expectation value
  have hself : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have hcz : z - conj z = Complex.I * hbar := by
    have hzc : conj z = inner ℂ (P psi - b • psi) (X psi - a • psi) := by
      rw [hz, inner_conj_symm]
    have hXP : (inner ℂ (X psi) (P psi) : ℂ) = inner ℂ psi (X (P psi)) := hX psi (P psi)
    have hPX : (inner ℂ (P psi) (X psi) : ℂ) = inner ℂ psi (P (X psi)) := hP psi (X psi)
    have hXs : (inner ℂ (X psi) psi : ℂ) = inner ℂ psi (X psi) := hX psi psi
    have hPs : (inner ℂ (P psi) psi : ℂ) = inner ℂ psi (P psi) := hP psi psi
    have hcomm' : (inner ℂ psi (X (P psi)) : ℂ) - inner ℂ psi (P (X psi)) = Complex.I * hbar := by
      rw [← inner_sub_right, hcomm psi, inner_smul_right, hself, mul_one]
    rw [hz, hzc]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, ha, hb]
    rw [hXP, hPX, hXs, hPs, hself]
    linear_combination hcomm'
  have him := congrArg Complex.im hcz
  simp at him
  linarith

/-- **Heisenberg uncertainty principle.**  Let `X` and `P` be symmetric (self-adjoint)
operators on a complex inner product space satisfying the canonical commutation relation
`[X, P] = i ℏ`.  Then for every normalized state `ψ`, the product of the uncertainties
`Δx = ‖(X - ⟪X⟫)ψ‖` and `Δp = ‖(P - ⟪P⟫)ψ‖` satisfies `Δx · Δp ≥ ℏ/2`.

The proof combines the commutator identity with the Cauchy–Schwarz inequality
(`norm_inner_le_norm`). -/
theorem heisenberg_uncertainty {X P : H →ₗ[ℂ] H}
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P) (hbar : ℝ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    stdDev X psi * stdDev P psi ≥ hbar / 2 := by
  have him := inner_im_eq hX hP hbar hcomm psi hpsi
  set u : H := X psi - ((mean X psi : ℝ) : ℂ) • psi with hu
  set v : H := P psi - ((mean P psi : ℝ) : ℂ) • psi with hv
  have h1 : hbar / 2 ≤ ‖(inner ℂ u v : ℂ)‖ := by
    rw [← him]
    exact le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have h2 : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  simpa [stdDev, hu, hv, ge_iff_le] using h1.trans h2

end QPhys

