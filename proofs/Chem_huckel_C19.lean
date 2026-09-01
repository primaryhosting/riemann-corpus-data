import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

open Matrix SimpleGraph

/-- A primitive 19-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

/-- The (unnormalised) discrete Fourier transform matrix on `Fin 19`. -/
noncomputable def dft19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun i k => om ^ (i.val * k.val)

/-- The Hückel eigenvalues of the cyclic polyene `C₁₉`. -/
noncomputable def eig19 (k : Fin 19) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 19) : ℝ) : ℂ)

theorem om_primitive : IsPrimitiveRoot om 19 :=
  Complex.isPrimitiveRoot_exp 19 (by norm_num)

theorem om_pow_19 : om ^ 19 = 1 := om_primitive.pow_eq_one

theorem om_ne_zero : om ≠ 0 := by
  simp [om, Complex.exp_ne_zero]

theorem om_pow_congr {a b : ℕ} (h : a % 19 = b % 19) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 19]
  conv_rhs => rw [← Nat.div_add_mod b 19]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_19, one_pow, one_pow, h]

theorem om_pow_mul_19 (m : ℕ) : (om ^ m) ^ 19 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, om_pow_19, one_pow]

/-- A right inverse of the DFT matrix. -/
noncomputable def dft19inv : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun k j => (19 : ℂ)⁻¹ * (om ^ (k.val * j.val))⁻¹

theorem dft19_mul_inv : dft19 * dft19inv = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  have hz : ∀ k : Fin 19,
      dft19 i k * dft19inv k l = (19 : ℂ)⁻¹ * (om ^ i.val * (om ^ l.val)⁻¹) ^ k.val := by
    intro k
    have hA : (om ^ i.val * (om ^ l.val)⁻¹) ^ k.val
        = om ^ (i.val * k.val) * (om ^ (k.val * l.val))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm l.val k.val]
    simp only [dft19, dft19inv, Matrix.of_apply, hA]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hz k), ← Finset.mul_sum]
  set z : ℂ := om ^ i.val * (om ^ l.val)⁻¹ with hzdef
  have hsum : ∑ k : Fin 19, z ^ k.val = ∑ k ∈ Finset.range 19, z ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => z ^ k) 19
  rw [hsum]
  by_cases hil : i = l
  · subst hil
    have hz1 : z = 1 := by
      rw [hzdef]
      field_simp
      exact div_self (pow_ne_zero _ om_ne_zero)
    rw [hz1]
    simp
  · have hne : z ≠ 1 := by
      rw [hzdef]
      intro h
      have hl : om ^ l.val ≠ 0 := pow_ne_zero _ om_ne_zero
      have heq : om ^ i.val = om ^ l.val := by
        field_simp at h
        exact h
      exact hil (Fin.ext (om_primitive.pow_inj i.isLt l.isLt heq))
    have hz19 : z ^ 19 = 1 := by
      have h2 : ((om ^ l.val)⁻¹) ^ 19 = 1 := by
        rw [inv_pow, om_pow_mul_19, inv_one]
      rw [hzdef, mul_pow, om_pow_mul_19, h2, one_mul]
    rw [geom_sum_eq hne, hz19]
    simp [hil]

theorem isUnit_dft19 : IsUnit dft19 := by
  refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
  have hdet : dft19.det * dft19inv.det = 1 := by
    rw [← Matrix.det_mul, dft19_mul_inv, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hdet

theorem om_pow_eq_exp (m : ℕ) :
    om ^ m = Complex.exp (((2 * Real.pi * (m : ℝ) / 19 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem eig19_eq (k : Fin 19) : om ^ (18 * k.val) + om ^ k.val = eig19 k := by
  have h1 : om ^ (18 * k.val) * om ^ k.val = 1 := by
    rw [← pow_add, show 18 * k.val + k.val = 19 * k.val by ring, pow_mul, om_pow_19, one_pow]
  have hkey : om ^ (18 * k.val) = (om ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hkey, om_pow_eq_exp k.val, ← Complex.exp_neg, eig19]
  push_cast
  rw [Complex.cos]
  ring_nf

theorem adj_mul_dft19 :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ * dft19 = dft19 * Matrix.diagonal eig19 := by
  ext i k
  have hlhs : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ * dft19) i k
      = ∑ u ∈ (SimpleGraph.cycleGraph 19).neighborFinset i, dft19 u k := by
    rw [Matrix.mul_apply]
    have h := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 19) i
      (fun j => dft19 j k)
    rw [← h]
    rfl
  rw [hlhs]
  have hnb : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i)
  rw [hnb]
  have hne : i - 1 ≠ i + 1 := by
    simp only [ne_eq, Fin.ext_iff, Fin.sub_def, Fin.add_def]
    omega
  rw [Finset.sum_pair hne, Matrix.mul_diagonal]
  have e1 : dft19 (i - 1) k = om ^ (18 * k.val) * om ^ (i.val * k.val) := by
    have hv : (i - 1 : Fin 19).val = (18 + i.val) % 19 := by
      rw [Fin.sub_def]; simp
    simp only [dft19, Matrix.of_apply, hv]
    rw [← pow_add]
    refine om_pow_congr ?_
    rw [show 18 * k.val + i.val * k.val = (18 + i.val) * k.val by ring]
    exact Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  have e2 : dft19 (i + 1) k = om ^ (i.val * k.val) * om ^ k.val := by
    have hv : (i + 1 : Fin 19).val = (i.val + 1) % 19 := by
      rw [Fin.add_def]; simp
    simp only [dft19, Matrix.of_apply, hv]
    rw [← pow_add]
    refine om_pow_congr ?_
    rw [show i.val * k.val + k.val = (i.val + 1) * k.val by ring]
    exact Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  have e0 : dft19 i k = om ^ (i.val * k.val) := rfl
  rw [e1, e2, e0, ← eig19_eq k]
  ring

/-- **Hückel theory for the cyclic polyene C₁₉.**
The spectrum of the adjacency matrix of the cycle graph `C₁₉` is exactly
`{2 cos (2πk/19) : k = 0, …, 18}`. -/
theorem huckel_C19 :
    spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ)
      = Set.range (fun k : Fin 19 =>
          ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 19) : ℝ) : ℂ)) := by
  obtain ⟨u, hus⟩ := isUnit_dft19
  have hconj : (u : Matrix (Fin 19) (Fin 19) ℂ) * Matrix.diagonal eig19
      * ((u⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) : Matrix (Fin 19) (Fin 19) ℂ)
      = (SimpleGraph.cycleGraph 19).adjMatrix ℂ := by
    rw [Units.mul_inv_eq_iff_eq_mul, hus]
    exact adj_mul_dft19.symm
  calc spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ)
      = spectrum ℂ ((u : Matrix (Fin 19) (Fin 19) ℂ) * Matrix.diagonal eig19
          * ((u⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) : Matrix (Fin 19) (Fin 19) ℂ)) := by
        rw [hconj]
    _ = spectrum ℂ (Matrix.diagonal eig19) := spectrum.units_conjugate
    _ = Set.range eig19 := spectrum_diagonal eig19

end Chem

