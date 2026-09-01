import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/
def adjC13 : Matrix (ZMod 13) (ZMod 13) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The standard primitive 13-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 13)

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 13 :=
  Complex.isPrimitiveRoot_exp 13 (by norm_num)

lemma zeta_pow13 : zeta ^ 13 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_mod (a : ℕ) : zeta ^ (a % 13) = zeta ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 13]
  rw [pow_add, pow_mul, zeta_pow13, one_pow, one_mul]

/-- The additive character `x ↦ ζ ^ x` of `ZMod 13`. -/
noncomputable def ee (x : ZMod 13) : ℂ := zeta ^ x.val

lemma ee_add (x y : ZMod 13) : ee (x + y) = ee x * ee y := by
  simp only [ee, ZMod.val_add, zeta_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (x : ZMod 13) : ee x ≠ 0 := by
  have : zeta ≠ 0 := by
    simp [zeta, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

lemma ee_neg (x : ZMod 13) : ee (-x) = (ee x)⁻¹ := by
  have h : ee x * ee (-x) = 1 := by rw [← ee_add]; simp [ee_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma sum_zmod_val (f : ℕ → ℂ) : ∑ k : ZMod 13, f k.val = ∑ j ∈ Finset.range 13, f j := by
  refine Finset.sum_nbij' (fun k => k.val) (fun j => (j : ZMod 13)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp [Finset.mem_range, ZMod.val_lt]
  · intro a _; simp
  · intro a _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro a ha; simp only [Finset.mem_range] at ha; exact ZMod.val_cast_of_lt ha
  · intro a _; rfl

/-- The sum of the character over all of `ZMod 13` vanishes. -/
lemma sum_ee : ∑ k : ZMod 13, ee k = 0 := by
  have := sum_zmod_val (fun j => zeta ^ j)
  simpa [ee] using this.trans (zeta_isPrimitiveRoot.geom_sum_eq_zero (by norm_num))

lemma sum_ee_mul (d : ZMod 13) : ∑ k : ZMod 13, ee (k * d) = if d = 0 then 13 else 0 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero, Finset.card_univ]
  · rw [if_neg hd]
    rw [← sum_ee]
    exact Fintype.sum_equiv (Equiv.mulRight₀ d hd) _ _ (fun k => rfl)

/-- The (unnormalised) discrete Fourier transform matrix. -/
noncomputable def dft : Matrix (ZMod 13) (ZMod 13) ℂ := fun i k => ee (i * k)

/-- Its (unnormalised) inverse. -/
noncomputable def dftInv : Matrix (ZMod 13) (ZMod 13) ℂ := fun k j => ee (-(k * j))

/-- The eigenvalues. -/
noncomputable def mu (k : ZMod 13) : ℂ := ee k + ee (-k)

lemma dft_mul_dftInv : dft * dftInv = (13 : ℂ) • (1 : Matrix (ZMod 13) (ZMod 13) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : ZMod 13, dft i k * dftInv k j = ee (k * (i - j)) := by
    intro k
    simp only [dft, dftInv, ← ee_add]
    congr 1
    ring
  simp_rw [hterm, sum_ee_mul, sub_eq_zero]
  by_cases h : i = j <;> simp [h]

lemma dft_det_ne_zero : dft.det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det dft_mul_dftInv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h2
  have hcard : Fintype.card (ZMod 13) = 13 := by simp
  rw [hcard] at h2
  norm_num at h2

lemma adj_mul_dft : adjC13 * dft = dft * Matrix.diagonal mu := by
  ext i k
  have hne : (i + 1 : ZMod 13) ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 13) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  have hterm : ∀ j : ZMod 13, adjC13 i j * dft j k =
      (if j = i + 1 then dft j k else 0) + (if j = i - 1 then dft j k else 0) := by
    intro j
    by_cases h1 : j = i + 1
    · subst h1
      simp [adjC13, hne]
    · by_cases h2 : j = i - 1
      · subst h2
        simp [adjC13, Ne.symm hne]
      · simp [adjC13, h1, h2]
  rw [Matrix.mul_apply]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => dft j k),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => dft j k)]
  simp only [Finset.mem_univ, if_true, Matrix.mul_diagonal]
  show ee ((i + 1) * k) + ee ((i - 1) * k) = ee (i * k) * mu k
  have e1 : (i + 1) * k = i * k + k := by ring
  have e2 : (i - 1) * k = i * k + (-k) := by ring
  rw [e1, e2, ee_add, ee_add, mu, mul_add]

lemma det_adj_sub (lam : ℂ) :
    (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det = ∏ k : ZMod 13, (mu k - lam) := by
  have key : (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)) * dft =
      dft * (Matrix.diagonal mu - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)) := by
    rw [sub_mul, mul_sub, adj_mul_dft, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h1 : (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det =
      (Matrix.diagonal mu - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det := by
    exact mul_right_cancel₀ dft_det_ne_zero (hdet.trans (mul_comm _ _))
  rw [h1, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.det_diagonal]

lemma mu_eq (k : ZMod 13) : mu k = 2 * Real.cos (2 * Real.pi * k.val / 13) := by
  have hz : ee k = Complex.exp ((2 * Real.pi * k.val / 13 : ℝ) * Complex.I) := by
    rw [ee, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mu, ee_neg, hz, Complex.ofReal_cos, Complex.two_cos, ← Complex.exp_neg]
  ring_nf

/-- **Hückel theory for the cycle `C₁₃`.**  A complex number `lam` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` (i.e. there is a nonzero vector `v` with
`A v = lam v`) if and only if `lam = 2 cos (2 π k / 13)` for some `k = 0, …, 12`. -/
theorem huckel_C13 (lam : ℂ) :
    (∃ v : ZMod 13 → ℂ, v ≠ 0 ∧ adjC13 *ᵥ v = lam • v) ↔
      ∃ k : ℕ, k < 13 ∧ lam = 2 * Real.cos (2 * Real.pi * k / 13) := by
  have hiff : ∀ v : ZMod 13 → ℂ,
      adjC13 *ᵥ v = lam • v ↔ (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)) *ᵥ v = 0 := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨v, hv, hveq⟩
    have hdet : (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, (hiff v).mp hveq⟩
    rw [det_adj_sub] at hdet
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hdet
    rw [sub_eq_zero] at hk
    exact ⟨k.val, ZMod.val_lt k, by rw [← hk, mu_eq]⟩
  · rintro ⟨k, hk, rfl⟩
    have hmu : mu (k : ZMod 13) = 2 * (Real.cos (2 * Real.pi * k / 13) : ℂ) := by
      rw [mu_eq, ZMod.val_cast_of_lt hk]
    have hdet : (adjC13 -
        (2 * (Real.cos (2 * Real.pi * k / 13) : ℂ)) • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det
        = 0 := by
      rw [det_adj_sub]
      exact Finset.prod_eq_zero (Finset.mem_univ (k : ZMod 13)) (by rw [sub_eq_zero, hmu])
    obtain ⟨v, hv, hveq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact ⟨v, hv, (hiff v).mpr hveq⟩

end Chem

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

