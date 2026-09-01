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
# The Fourier spectrum of the combinatorial cycle Laplacian

For `n : ℕ` we work in the finite dimensional complex vector space `Fin n → ℂ` and
study the combinatorial Laplacian of the cycle graph `C n`,

  `(L v) j = 2 * v j - v (j + 1) - v (j - 1)`,

where the indices are taken in `Fin n`, i.e. cyclically (see `cycleLaplacian_apply`).
The intended range of `n` is `3 ≤ n`, but everything below is proved for every
`n ≠ 0`; the exported theorem `cycle_laplacian_spectrum` is stated for `3 ≤ n`.

The discrete Fourier vectors `vₖ j = exp (2 π I k j / n)` are eigenvectors of `L`
with eigenvalues `2 - 2 cos (2 π k / n)`, they are pairwise orthogonal, and they
form a basis of `Fin n → ℂ`.  Consequently the spectrum of `L` is exactly the set
of these numbers, and both the geometric and the algebraic multiplicity of each
eigenvalue are given by the number of Fourier modes producing it.

Main results:

* `Frontier.Spectral.fourierVec_ne_zero` — each Fourier vector is nonzero;
* `Frontier.Spectral.cycleLaplacian_fourierVec` — the eigenvalue equation;
* `Frontier.Spectral.fourierVec_orthogonal`, `Frontier.Spectral.fourierVec_inner_euclidean`,
  `Frontier.Spectral.fourierBasis` — orthogonality and the resulting basis;
* `Frontier.Spectral.finrank_eigenspace`, `Frontier.Spectral.charpoly_cycleLaplacian` —
  geometric and algebraic multiplicities;
* `Frontier.Spectral.cycle_laplacian_spectrum` — the exported spectral theorem.

This is the standard finite-dimensional spectral computation for the cycle graph; no new
mathematics is claimed, and in particular nothing is claimed about uniform spectral gaps
of families of graphs.

Scope and limitations (honest summary):

* `spectrum` is Mathlib's `spectrum ℂ (f : Module.End ℂ (Fin n → ℂ))`, i.e. the set of `μ`
  for which `μ • 1 - f` is not invertible.  No bespoke notion of spectrum is introduced.
* Orthogonality is stated as the explicit Hermitian sum `∑ j, conj (vₗ j) * vₖ j`, since the
  plain pi type `Fin n → ℂ` carries no inner product instance in Mathlib; the corresponding
  statement for Mathlib's inner product on `EuclideanSpace ℂ (Fin n)` is
  `fourierVec_inner_euclidean`.
* The Fourier vectors are orthogonal but not normalised: `∑ j, conj (vₖ j) * vₖ j = n`
  (`fourierVec_inner`).
* The proofs only use `n ≠ 0`; the hypothesis `3 ≤ n` in the exported theorem is kept
  because the cycle graph `C n` is a simple graph only for `n ≥ 3`.
* Multiplicities are covered in two ways: geometric multiplicity by `finrank_eigenspace`
  and algebraic multiplicity by `charpoly_cycleLaplacian`.  Distinct values of `k` may of
  course give the same eigenvalue (`k` and `n - k` do), which is exactly what those two
  statements account for.
-/

namespace Frontier.Spectral

open Complex Finset

/-! ### The root of unity -/

/-- The standard primitive `n`-th root of unity. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem isPrimitiveRoot_zeta (n : ℕ) (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

theorem zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

theorem zeta_pow_self (n : ℕ) (hn : n ≠ 0) : zeta n ^ n = 1 :=
  (isPrimitiveRoot_zeta n hn).pow_eq_one

theorem zeta_norm (n : ℕ) : ‖zeta n‖ = 1 := by
  have h : zeta n = Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) := by
    rw [zeta]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem conj_zeta (n : ℕ) : (starRingEnd ℂ) (zeta n) = (zeta n)⁻¹ :=
  (Complex.inv_eq_conj (zeta_norm n)).symm

/-- Powers of `zeta n` only depend on the exponent modulo `n`. -/
theorem zeta_pow_congr (n a b : ℕ) (hn : n ≠ 0) (hab : a % n = b % n) :
    zeta n ^ a = zeta n ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  conv_rhs => rw [← Nat.div_add_mod b n]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta_pow_self n hn, one_pow, one_pow, hab]

/-! ### Definitions -/

/-- The combinatorial Laplacian of the `n`-cycle, as a linear endomorphism of `Fin n → ℂ`.
Both index shifts are taken in `Fin n`, i.e. cyclically. -/
noncomputable def cycleLaplacian (n : ℕ) : Module.End ℂ (Fin n → ℂ) where
  toFun v := fun j => haveI : NeZero n := ⟨j.pos.ne'⟩; 2 * v j - v (j + 1) - v (j - 1)
  map_add' u v := by funext j; haveI : NeZero n := ⟨j.pos.ne'⟩; simp; ring
  map_smul' c v := by funext j; haveI : NeZero n := ⟨j.pos.ne'⟩; simp; ring

@[simp] theorem cycleLaplacian_apply (n : ℕ) [NeZero n] (v : Fin n → ℂ) (j : Fin n) :
    cycleLaplacian n v j = 2 * v j - v (j + 1) - v (j - 1) := rfl

/-- The `k`-th discrete Fourier vector on the `n`-cycle. -/
noncomputable def fourierVec (n : ℕ) (k : Fin n) : Fin n → ℂ := fun j =>
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℝ) : ℂ) * (((j : ℕ) : ℝ) : ℂ)
    / (((n : ℕ) : ℝ) : ℂ))

/-- The `k`-th Laplacian eigenvalue on the `n`-cycle. -/
noncomputable def cycleEigenvalue (n : ℕ) (k : Fin n) : ℂ :=
  ((2 - 2 * Real.cos (2 * Real.pi * ((k : ℕ) : ℝ) / ((n : ℕ) : ℝ)) : ℝ) : ℂ)

/-! ### Basic properties of the Fourier vectors -/

theorem fourierVec_eq_zeta_pow (n : ℕ) (k j : Fin n) :
    fourierVec n k j = zeta n ^ ((k : ℕ) * (j : ℕ)) := by
  rw [zeta, ← Complex.exp_nat_mul, fourierVec]
  congr 1
  push_cast
  ring

/-- (1) Each Fourier vector is nonzero. -/
theorem fourierVec_ne_zero (n : ℕ) (k : Fin n) : fourierVec n k ≠ 0 := by
  intro h
  have hk := congrFun h k
  simp [fourierVec, Complex.exp_ne_zero] at hk

theorem fourierVec_next (n : ℕ) [NeZero n] (k j : Fin n) :
    fourierVec n k (j + 1) = zeta n ^ (k : ℕ) * fourierVec n k j := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [fourierVec_eq_zeta_pow, fourierVec_eq_zeta_pow]
  have hv : ((j + 1 : Fin n) : ℕ) = ((j : ℕ) + 1) % n := by simp [Fin.val_add]
  have h2 : zeta n ^ (k : ℕ) * zeta n ^ ((k : ℕ) * (j : ℕ))
      = zeta n ^ ((k : ℕ) * ((j : ℕ) + 1)) := by
    rw [← pow_add]; ring_nf
  rw [hv, h2]
  exact zeta_pow_congr n _ _ hn (Nat.ModEq.mul_left _ (Nat.mod_modEq _ n))

theorem fourierVec_prev (n : ℕ) [NeZero n] (k j : Fin n) :
    zeta n ^ (k : ℕ) * fourierVec n k (j - 1) = fourierVec n k j := by
  rw [← fourierVec_next, sub_add_cancel]

theorem two_sub_zeta_pow_sub_inv (n : ℕ) (hn : n ≠ 0) (k : Fin n) :
    2 - zeta n ^ (k : ℕ) - (zeta n ^ (k : ℕ))⁻¹ = cycleEigenvalue n k := by
  have hn' : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set θ : ℝ := 2 * Real.pi * ((k : ℕ) : ℝ) / ((n : ℕ) : ℝ) with hθ
  have h1 : zeta n ^ (k : ℕ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    field_simp
  rw [h1, ← Complex.exp_neg, cycleEigenvalue, ← hθ]
  push_cast
  rw [Complex.cos, neg_mul]
  ring

/-- (2) The Fourier vectors are eigenvectors of the cycle Laplacian. -/
theorem cycleLaplacian_fourierVec (n : ℕ) (k : Fin n) :
    cycleLaplacian n (fourierVec n k) = cycleEigenvalue n k • fourierVec n k := by
  have hn : n ≠ 0 := k.pos.ne'
  haveI : NeZero n := ⟨hn⟩
  have hw : zeta n ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
  funext j
  have hprev : fourierVec n k (j - 1) = (zeta n ^ (k : ℕ))⁻¹ * fourierVec n k j := by
    rw [← fourierVec_prev n k j]
    field_simp
  simp only [cycleLaplacian_apply, Pi.smul_apply, smul_eq_mul, fourierVec_next, hprev]
  rw [← two_sub_zeta_pow_sub_inv n hn k]
  ring

/-! ### Orthogonality -/

/-- The hermitian inner product of two Fourier vectors: `n` if they agree, `0` otherwise. -/
theorem fourierVec_inner (n : ℕ) (k l : Fin n) :
    ∑ j : Fin n, (starRingEnd ℂ) (fourierVec n l j) * fourierVec n k j
      = if k = l then (n : ℂ) else 0 := by
  have hn : n ≠ 0 := k.pos.ne'
  have hz : zeta n ≠ 0 := zeta_ne_zero n
  set y : ℂ := zeta n ^ (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) with hy
  have key : ∀ j : Fin n,
      (starRingEnd ℂ) (fourierVec n l j) * fourierVec n k j = y ^ (j : ℕ) := by
    intro j
    rw [fourierVec_eq_zeta_pow, fourierVec_eq_zeta_pow, map_pow, conj_zeta]
    have e1 : ((zeta n)⁻¹) ^ ((l : ℕ) * (j : ℕ))
        = zeta n ^ (-(((l : ℕ) * (j : ℕ) : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    have e2 : zeta n ^ ((k : ℕ) * (j : ℕ)) = zeta n ^ ((((k : ℕ) * (j : ℕ) : ℕ)) : ℤ) :=
      (zpow_natCast _ _).symm
    have e3 : y ^ (j : ℕ) = zeta n ^ ((((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) * ((j : ℕ) : ℤ)) := by
      rw [hy, ← zpow_natCast (zeta n ^ _) (j : ℕ), ← zpow_mul]
    rw [e1, e2, e3, ← zpow_add₀ hz]
    congr 1
    push_cast
    ring
  simp only [key]
  rw [Fin.sum_univ_eq_sum_range (fun i => y ^ i) n]
  by_cases h : k = l
  · subst h
    simp [hy]
  · rw [if_neg h]
    have hyne : y ≠ 1 := by
      intro h1
      have hdvd : ((n : ℕ) : ℤ) ∣ (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) :=
        ((isPrimitiveRoot_zeta n hn).zpow_eq_one_iff_dvd _).mp h1
      have habs : |(((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))| < (n : ℤ) := by
        have := k.isLt; have := l.isLt
        rw [abs_lt]; omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact h (Fin.ext (by omega))
    have hyn : y ^ n = 1 := by
      rw [hy, ← zpow_natCast (zeta n ^ _) n, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, zeta_pow_self n hn, one_zpow]
    rw [geom_sum_eq hyne, hyn, sub_self, zero_div]

/-- (3a) Distinct Fourier vectors are orthogonal. -/
theorem fourierVec_orthogonal (n : ℕ) (k l : Fin n) (hkl : k ≠ l) :
    ∑ j : Fin n, (starRingEnd ℂ) (fourierVec n l j) * fourierVec n k j = 0 := by
  rw [fourierVec_inner n k l, if_neg hkl]

/-- (3a') The same orthogonality statement, phrased with the Hermitian inner product of
the Euclidean space `EuclideanSpace ℂ (Fin n)` (whose underlying type is `Fin n → ℂ`). -/
theorem fourierVec_inner_euclidean (n : ℕ) (k l : Fin n) (hkl : k ≠ l) :
    inner ℂ ((WithLp.toLp 2 (fourierVec n l) : EuclideanSpace ℂ (Fin n)))
      (WithLp.toLp 2 (fourierVec n k)) = 0 := by
  rw [show inner ℂ ((WithLp.toLp 2 (fourierVec n l) : EuclideanSpace ℂ (Fin n)))
        (WithLp.toLp 2 (fourierVec n k))
      = ∑ j : Fin n, (starRingEnd ℂ) (fourierVec n l j) * fourierVec n k j by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]]
  exact fourierVec_orthogonal n k l hkl

/-- (3b) The Fourier vectors are linearly independent. -/
theorem fourierVec_linearIndependent (n : ℕ) (hn : n ≠ 0) :
    LinearIndependent ℂ (fourierVec n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h1 : ∀ j : Fin n, ∑ k, g k * fourierVec n k j = 0 := by
    intro j
    have h := congrFun hg j
    simpa [Finset.sum_apply] using h
  have h3 : ∑ k, g k * (if k = l then (n : ℂ) else 0) = 0 := by
    calc ∑ k, g k * (if k = l then (n : ℂ) else 0)
        = ∑ k, ∑ j, g k * ((starRingEnd ℂ) (fourierVec n l j) * fourierVec n k j) := by
          simp only [← fourierVec_inner n _ l, Finset.mul_sum]
      _ = ∑ j, (starRingEnd ℂ) (fourierVec n l j) * ∑ k, g k * fourierVec n k j := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
          congr 1; ext j; congr 1; ext k; ring
      _ = 0 := by simp [h1]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ l] at h3
  simp only [Finset.mem_univ, if_true, mul_eq_zero] at h3
  rcases h3 with h | h
  · exact h
  · exact absurd h (Nat.cast_ne_zero.mpr hn)

/-- (3c) The Fourier basis of `Fin n → ℂ`. -/
noncomputable def fourierBasis (n : ℕ) (hn : n ≠ 0) : Module.Basis (Fin n) ℂ (Fin n → ℂ) :=
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (fourierVec_linearIndependent n hn)
    (by simp)

@[simp] theorem fourierBasis_apply (n : ℕ) (hn : n ≠ 0) (k : Fin n) :
    fourierBasis n hn k = fourierVec n k := by
  simp [fourierBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ### Diagonalisation -/

/-- In the Fourier basis the Laplacian acts diagonally on coordinates. -/
theorem repr_cycleLaplacian (n : ℕ) (hn : n ≠ 0) (u : Fin n → ℂ) (k : Fin n) :
    (fourierBasis n hn).repr (cycleLaplacian n u) k
      = cycleEigenvalue n k * (fourierBasis n hn).repr u k := by
  set b := fourierBasis n hn with hb
  have h1 : cycleLaplacian n u = ∑ i, (cycleEigenvalue n i * b.repr u i) • b i := by
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul, hb, fourierBasis_apply, cycleLaplacian_fourierVec, smul_smul, mul_comm]
  rw [h1]
  exact congrFun (b.repr_sum_self _) k

/-- Characterisation of eigenvectors in terms of Fourier coordinates. -/
theorem cycleLaplacian_eq_smul_iff (n : ℕ) (hn : n ≠ 0) (u : Fin n → ℂ) (μ : ℂ) :
    cycleLaplacian n u = μ • u ↔
      ∀ k : Fin n, (cycleEigenvalue n k - μ) * (fourierBasis n hn).repr u k = 0 := by
  constructor
  · intro h k
    have hk := congrArg (fun w => (fourierBasis n hn).repr w k) h
    simp only [repr_cycleLaplacian, map_smul, Finsupp.smul_apply, smul_eq_mul] at hk
    rw [sub_mul, hk, sub_self]
  · intro h
    apply (fourierBasis n hn).repr.injective
    ext k
    have hk := h k
    rw [sub_mul, sub_eq_zero] at hk
    simp only [repr_cycleLaplacian, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact hk

/-! ### The spectrum -/

/-- Every Fourier eigenvalue lies in the spectrum. -/
theorem cycleEigenvalue_mem_spectrum (n : ℕ) (k : Fin n) :
    cycleEigenvalue n k ∈ spectrum ℂ (cycleLaplacian n) := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := fourierVec n k) ⟨?_, fourierVec_ne_zero n k⟩
  exact Module.End.mem_eigenspace_iff.mpr (cycleLaplacian_fourierVec n k)

/-- Every element of the spectrum is one of the Fourier eigenvalues. -/
theorem spectrum_subset_cycleEigenvalues (n : ℕ) (hn : n ≠ 0) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (cycleLaplacian n)) : ∃ k : Fin n, μ = cycleEigenvalue n k := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨u, hu, hu0⟩ := hμ.exists_hasEigenvector
  have h1 := (cycleLaplacian_eq_smul_iff n hn u μ).mp (Module.End.mem_eigenspace_iff.mp hu)
  have hrep : (fourierBasis n hn).repr u ≠ 0 := by
    intro h
    exact hu0 ((fourierBasis n hn).repr.injective (by simpa using h))
  obtain ⟨k, hk⟩ : ∃ k, (fourierBasis n hn).repr u k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hrep (by ext k; simpa using hcon k)
  rcases mul_eq_zero.mp (h1 k) with h | h
  · exact ⟨k, (sub_eq_zero.mp h).symm⟩
  · exact absurd h hk

/-- The eigenspace of `μ` is spanned by the Fourier vectors with eigenvalue `μ`. -/
theorem eigenspace_eq_span (n : ℕ) (hn : n ≠ 0) (μ : ℂ) :
    (cycleLaplacian n).eigenspace μ =
      Submodule.span ℂ
        (Set.range fun k : {k : Fin n // cycleEigenvalue n k = μ} => fourierVec n (k : Fin n)) := by
  apply le_antisymm
  · intro u hu
    have h1 := (cycleLaplacian_eq_smul_iff n hn u μ).mp (Module.End.mem_eigenspace_iff.mp hu)
    rw [← (fourierBasis n hn).sum_repr u]
    refine Submodule.sum_mem _ ?_
    intro i _
    by_cases hi : cycleEigenvalue n i = μ
    · rw [fourierBasis_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · have hzero : (fourierBasis n hn).repr u i = 0 := by
        rcases mul_eq_zero.mp (h1 i) with h | h
        · exact absurd (sub_eq_zero.mp h) hi
        · exact h
      simp [hzero]
  · rw [Submodule.span_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (by rw [cycleLaplacian_fourierVec, hk])

/-- (4') Geometric multiplicity: the dimension of the `μ`-eigenspace is the number of
Fourier modes with eigenvalue `μ`. -/
theorem finrank_eigenspace (n : ℕ) (hn : n ≠ 0) (μ : ℂ) :
    Module.finrank ℂ ((cycleLaplacian n).eigenspace μ) =
      Nat.card {k : Fin n // cycleEigenvalue n k = μ} := by
  classical
  haveI : Fintype {k : Fin n // cycleEigenvalue n k = μ} := Fintype.ofFinite _
  rw [eigenspace_eq_span n hn, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card
    ((fourierVec_linearIndependent n hn).comp _ Subtype.val_injective)

/-- (4'') Algebraic multiplicity: the characteristic polynomial of the cycle Laplacian
factors as the product over all Fourier modes. -/
theorem charpoly_cycleLaplacian (n : ℕ) (hn : n ≠ 0) :
    (cycleLaplacian n).charpoly =
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (cycleEigenvalue n k)) := by
  have hmat : LinearMap.toMatrix (fourierBasis n hn) (fourierBasis n hn) (cycleLaplacian n)
      = Matrix.diagonal (cycleEigenvalue n) := by
    ext i j
    rw [LinearMap.toMatrix_apply, fourierBasis_apply, cycleLaplacian_fourierVec, map_smul,
      Finsupp.smul_apply, smul_eq_mul, ← fourierBasis_apply n hn,
      Module.Basis.repr_self_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← LinearMap.charpoly_toMatrix (cycleLaplacian n) (fourierBasis n hn), hmat,
    Matrix.charpoly_diagonal]

/-- (5) **Main theorem.** For `3 ≤ n` the spectrum of the combinatorial Laplacian of the
`n`-cycle is exactly `{2 - 2 cos (2 π k / n) : k ∈ Fin n}`.  (Only `n ≠ 0` is really
needed; the hypothesis `3 ≤ n` is kept because the cycle graph `C n` is a genuine simple
graph only for `n ≥ 3`.) -/
theorem cycle_laplacian_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      {μ : ℂ | ∃ k : Fin n,
        μ = ((2 - 2 * Real.cos (2 * Real.pi * ((k : ℕ) : ℝ) / ((n : ℕ) : ℝ)) : ℝ) : ℂ)} := by
  have h0 : n ≠ 0 := by omega
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := spectrum_subset_cycleEigenvalues n h0 μ h
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact cycleEigenvalue_mem_spectrum n k

/-- A sanity check (the spectrum is not empty): `0` is always an eigenvalue, with the
constant vector `fourierVec n 0` as eigenvector. -/
theorem zero_mem_spectrum (n : ℕ) (hn : n ≠ 0) :
    (0 : ℂ) ∈ spectrum ℂ (cycleLaplacian n) := by
  haveI : NeZero n := ⟨hn⟩
  have h := cycleEigenvalue_mem_spectrum n (0 : Fin n)
  simpa [cycleEigenvalue] using h

/-! ### Axiom audit -/

#print axioms cycle_laplacian_spectrum
#print axioms cycleLaplacian_fourierVec
#print axioms fourierVec_orthogonal
#print axioms fourierVec_linearIndependent
#print axioms finrank_eigenspace
#print axioms charpoly_cycleLaplacian

end Frontier.Spectral

