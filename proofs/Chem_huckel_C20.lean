/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₂₀`, indexed by `Fin 20`
(whose addition is addition modulo `20`). -/
def C20adj : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The `k`-th Hückel eigenvalue of `C₂₀`: `2 cos (2πk/20)`. -/
noncomputable def C20eig (k : Fin 20) : ℂ := 2 * Real.cos (2 * Real.pi * k / 20)

/-- A primitive 20-th root of unity. -/
noncomputable def zeta20 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

/-- The matrix whose `k`-th column is the eigenvector `i ↦ ζ^(ik)`. -/
noncomputable def C20vec : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.of fun i j => zeta20 ^ (i.val * j.val)

lemma zeta20_primitive : IsPrimitiveRoot zeta20 20 := by
  have := Complex.isPrimitiveRoot_exp 20 (by norm_num)
  simpa [zeta20] using this

lemma zeta20_pow_twenty : zeta20 ^ 20 = 1 := zeta20_primitive.pow_eq_one

lemma zeta20_pow_mod (a : ℕ) : zeta20 ^ a = zeta20 ^ (a % 20) := by
  conv_lhs => rw [← Nat.div_add_mod a 20]
  rw [pow_add, pow_mul, zeta20_pow_twenty, one_pow, one_mul]

lemma Fin20_add_one_val (i : Fin 20) : (i + 1).val = (i.val + 1) % 20 := by
  simp [Fin.add_def]

lemma Fin20_sub_one_val (i : Fin 20) : (i - 1).val = (i.val + 19) % 20 := by
  simp [Fin.sub_def, Nat.add_comm]

lemma Fin20_add_one_ne_sub_one (i : Fin 20) : i + 1 ≠ i - 1 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin20_add_one_val, Fin20_sub_one_val] at h'
  omega

lemma zeta20_pow_inv (m : ℕ) : zeta20 ^ (19 * m) = (zeta20 ^ m)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, show 19 * m + m = 20 * m by ring, pow_mul, zeta20_pow_twenty, one_pow]

lemma C20eig_eq (k : Fin 20) : C20eig k = zeta20 ^ k.val + zeta20 ^ (19 * k.val) := by
  have hx : zeta20 ^ k.val = Complex.exp (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta20, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [C20eig, zeta20_pow_inv, hx, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

lemma zeta20_pow_add_one (i k : Fin 20) :
    zeta20 ^ ((i + 1).val * k.val) = zeta20 ^ ((i.val + 1) * k.val) := by
  rw [zeta20_pow_mod, zeta20_pow_mod ((i.val + 1) * k.val), Fin20_add_one_val]
  exact congrArg _ ((Nat.mod_modEq (i.val + 1) 20).mul_right k.val)

lemma zeta20_pow_sub_one (i k : Fin 20) :
    zeta20 ^ ((i - 1).val * k.val) = zeta20 ^ ((i.val + 19) * k.val) := by
  rw [zeta20_pow_mod, zeta20_pow_mod ((i.val + 19) * k.val), Fin20_sub_one_val]
  exact congrArg _ ((Nat.mod_modEq (i.val + 19) 20).mul_right k.val)

lemma C20adj_mul_C20vec : C20adj * C20vec = C20vec * Matrix.diagonal C20eig := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have hsplit : ∀ j : Fin 20, C20adj i j * C20vec j k
      = (if j = i + 1 then zeta20 ^ (j.val * k.val) else 0)
        + (if j = i - 1 then zeta20 ^ (j.val * k.val) else 0) := by
    intro j
    rcases eq_or_ne j (i + 1) with h1 | h1
    · subst h1
      simp [C20adj, C20vec, Fin20_add_one_ne_sub_one i]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · subst h2
        simp [C20adj, C20vec, h1]
      · simp [C20adj, C20vec, h1, h2]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  rw [zeta20_pow_add_one, zeta20_pow_sub_one, C20eig_eq, C20vec, Matrix.of_apply,
    show (i.val + 1) * k.val = i.val * k.val + k.val by ring,
    show (i.val + 19) * k.val = i.val * k.val + 19 * k.val by ring, pow_add, pow_add]
  ring

lemma C20vec_eq_vandermonde :
    C20vec = Matrix.vandermonde (fun i : Fin 20 => zeta20 ^ (i : ℕ)) := by
  ext i j
  simp [C20vec, Matrix.vandermonde, ← pow_mul]

lemma C20vec_det_ne_zero : C20vec.det ≠ 0 := by
  rw [C20vec_eq_vandermonde]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext (zeta20_primitive.pow_inj i.isLt j.isLt hij)

/-- **Hückel theory for `C₂₀`.** A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₂₀` if and only if `μ = 2 cos (2πk/20)` for some `k = 0,…,19`. -/
theorem huckel_C20 (μ : ℂ) :
    (∃ v : Fin 20 → ℂ, v ≠ 0 ∧ C20adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 20, μ = 2 * Real.cos (2 * Real.pi * k / 20) := by
  have key : (C20adj - μ • (1 : Matrix (Fin 20) (Fin 20) ℂ)) * C20vec
      = C20vec * (Matrix.diagonal C20eig - μ • 1) := by
    rw [sub_mul, mul_sub, C20adj_mul_C20vec, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hdet : (C20adj - μ • (1 : Matrix (Fin 20) (Fin 20) ℂ)).det
      = (Matrix.diagonal C20eig - μ • 1).det := by
    have h := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul] at h
    exact mul_right_cancel₀ C20vec_det_ne_zero (h.trans (mul_comm _ _))
  have hdiag : (Matrix.diagonal C20eig - μ • (1 : Matrix (Fin 20) (Fin 20) ℂ))
      = Matrix.diagonal (fun k => C20eig k - μ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have hprod : (C20adj - μ • (1 : Matrix (Fin 20) (Fin 20) ℂ)).det
      = ∏ k : Fin 20, (C20eig k - μ) := by
    rw [hdet, hdiag, Matrix.det_diagonal]
  constructor
  · rintro ⟨v, hv, hAv⟩
    have h0 : (C20adj - μ • (1 : Matrix (Fin 20) (Fin 20) ℂ)) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv, sub_self]
    have hz : (C20adj - μ • (1 : Matrix (Fin 20) (Fin 20) ℂ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, h0⟩
    rw [hprod, Finset.prod_eq_zero_iff] at hz
    obtain ⟨k, -, hk⟩ := hz
    have h := sub_eq_zero.mp hk
    simp only [C20eig] at h
    exact ⟨k, h.symm⟩
  · rintro ⟨k, hk⟩
    have hz : (C20adj - μ • (1 : Matrix (Fin 20) (Fin 20) ℂ)).det = 0 := by
      rw [hprod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [C20eig, hk])
    obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0

#print axioms Chem.huckel_C20

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

