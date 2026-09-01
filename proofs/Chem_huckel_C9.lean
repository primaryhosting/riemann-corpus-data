/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 40000

namespace Chem

open Matrix Complex

/-- The primitive 9th root of unity `exp(2πi/9)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

lemma om_primitive : IsPrimitiveRoot om 9 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 9 (by norm_num)

lemma om_pow_nine : om ^ 9 = 1 := om_primitive.pow_eq_one

/-- The Hückel (adjacency) matrix of the cycle `C₉`. -/
noncomputable def C9 : Matrix (Fin 9) (Fin 9) ℂ := (SimpleGraph.cycleGraph 9).adjMatrix ℂ

/-- The discrete-Fourier (Vandermonde) matrix built from powers of `om`. -/
noncomputable def P : Matrix (Fin 9) (Fin 9) ℂ := Matrix.vandermonde (fun j : Fin 9 => om ^ (j : ℕ))

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/9)`. -/
noncomputable def Dg : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.diagonal (fun k : Fin 9 => ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ))

lemma om_pow_eq_exp (k : ℕ) : om ^ k = Complex.exp ((2 * Real.pi * k / 9 : ℝ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma two_cos_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ) = om ^ k + (om ^ k) ^ 8 := by
  have hz9 : (om ^ k) ^ 9 = 1 := by rw [pow_right_comm, om_pow_nine, one_pow]
  have hzne : om ^ k ≠ 0 := by
    intro h
    rw [h] at hz9
    simp at hz9
  have h8 : (om ^ k) ^ 8 = (om ^ k)⁻¹ := by
    field_simp
    linear_combination hz9
  rw [h8, om_pow_eq_exp k, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

lemma C9_mul_P : C9 * P = P * Dg := by
  ext i k
  set z : ℂ := om ^ (k : ℕ) with hz
  have hz9 : z ^ 9 = 1 := by rw [hz, pow_right_comm, om_pow_nine, one_pow]
  have hP : ∀ j : Fin 9, P j k = z ^ (j : ℕ) := by
    intro j
    simp [P, Matrix.vandermonde, hz, pow_right_comm]
  have hRHS : (P * Dg) i k = z ^ (i : ℕ) * (z + z ^ 8) := by
    rw [Dg, Matrix.mul_diagonal, hP i, hz, two_cos_eq (k : ℕ)]
  clear_value z
  clear hz
  rw [hRHS, Matrix.mul_apply]
  simp only [hP, C9, SimpleGraph.adjMatrix_apply]
  fin_cases i <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, SimpleGraph.cycleGraph_adj] <;>
    norm_num <;> simp +decide only [] <;> norm_num <;>
    first
      | ring1
      | linear_combination (-(1 : ℂ)) * hz9
      | linear_combination (-z) * hz9
      | linear_combination (-z ^ 2) * hz9
      | linear_combination (-z ^ 3) * hz9
      | linear_combination (-z ^ 4) * hz9
      | linear_combination (-z ^ 5) * hz9
      | linear_combination (-z ^ 6) * hz9
      | linear_combination (-z ^ 7) * hz9
      | linear_combination (-(1 : ℂ) - z ^ 7) * hz9

lemma P_isUnit : IsUnit P := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [P, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  simp only [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne ?_
  intro h
  have := om_primitive.pow_inj j.isLt i.isLt h
  omega

/-- **Hückel theory for the cycle `C₉`.**  The spectrum of the adjacency (Hückel) matrix of
the cycle graph `C₉` is exactly `{2 cos (2πk/9) : k = 0, …, 8}`. -/
theorem huckel_C9 :
    spectrum ℂ ((SimpleGraph.cycleGraph 9).adjMatrix ℂ) =
      {z : ℂ | ∃ k : Fin 9, z = ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ)} := by
  obtain ⟨u, hu⟩ := P_isUnit
  have hconj : C9 = (u : Matrix (Fin 9) (Fin 9) ℂ) * Dg * ((u⁻¹ : (Matrix (Fin 9) (Fin 9) ℂ)ˣ) : Matrix (Fin 9) (Fin 9) ℂ) := by
    rw [Units.eq_mul_inv_iff_mul_eq, hu]
    exact C9_mul_P
  have : spectrum ℂ C9 = spectrum ℂ Dg := by
    rw [hconj, spectrum.units_conjugate]
  rw [show (SimpleGraph.cycleGraph 9).adjMatrix ℂ = C9 from rfl, this, Dg, spectrum_diagonal]
  ext z
  simp [Set.mem_range, eq_comm]

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

