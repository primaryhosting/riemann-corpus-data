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

set_option grind.warning false

namespace Chem

open Matrix

/-- The standard additive character `x ↦ exp (2 π i x / 18)` on `ZMod 18`. -/
noncomputable def psi : AddChar (ZMod 18) ℂ := ZMod.stdAddChar

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertex set viewed as `ZMod 18`
(which is definitionally `Fin 18`). -/
noncomputable def cycAdj : Matrix (ZMod 18) (ZMod 18) ℂ :=
  (SimpleGraph.cycleGraph 18).adjMatrix ℂ

/-- The discrete Fourier matrix on `ZMod 18`. -/
noncomputable def dftMat : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun j k => psi (j * k)

/-- The inverse discrete Fourier matrix on `ZMod 18`. -/
noncomputable def dftInv : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun j k => (18 : ℂ)⁻¹ * psi (-(j * k))

/-- The `k`-th Hückel eigenvalue of `C₁₈`. -/
noncomputable def eigval (k : ZMod 18) : ℂ := psi k + psi (-k)

lemma psi_sum (t : ZMod 18) : ∑ i : ZMod 18, psi (t * i) = if t = 0 then 18 else 0 := by
  split_ifs with h
  · simp [h, psi]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 18 h)

lemma dft_mul_inv : dftMat * dftInv = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [dftMat, dftInv, Matrix.of_apply]
  have key : ∀ i : ZMod 18, psi (j * i) * ((18 : ℂ)⁻¹ * psi (-(i * k)))
      = (18 : ℂ)⁻¹ * psi ((j - k) * i) := by
    intro i
    rw [show (j - k) * i = j * i + -(i * k) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, psi_sum]
  by_cases hjk : j = k
  · simp [hjk, Matrix.one_apply]
  · rw [if_neg (sub_ne_zero_of_ne hjk), Matrix.one_apply_ne hjk, mul_zero]

lemma inv_mul_dft : dftInv * dftMat = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [dftMat, dftInv, Matrix.of_apply]
  have key : ∀ i : ZMod 18, (18 : ℂ)⁻¹ * psi (-(j * i)) * psi (i * k)
      = (18 : ℂ)⁻¹ * psi ((k - j) * i) := by
    intro i
    rw [show (k - j) * i = -(j * i) + i * k by ring, AddChar.map_add_eq_mul, mul_assoc]
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, psi_sum]
  by_cases hjk : j = k
  · simp [hjk, Matrix.one_apply]
  · rw [if_neg (sub_ne_zero_of_ne (fun h => hjk h.symm)), Matrix.one_apply_ne hjk, mul_zero]

lemma cyc_adj_iff : ∀ j m : ZMod 18,
    ((SimpleGraph.cycleGraph 18).Adj j m ↔ (m = j - 1 ∨ m = j + 1)) := by decide

lemma cycAdj_apply (j m : ZMod 18) :
    cycAdj j m = if (m = j - 1 ∨ m = j + 1) then 1 else 0 := by
  rw [cycAdj, SimpleGraph.adjMatrix_apply]
  simp only [cyc_adj_iff]

lemma sub_one_ne_add_one (j : ZMod 18) : j - 1 ≠ j + 1 := by
  intro h
  have h2 : (2 : ZMod 18) = 0 := by linear_combination (norm := ring_nf) -h
  exact absurd h2 (by decide)

lemma adj_mul_dft : cycAdj * dftMat = dftMat * Matrix.diagonal eigval := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have key : ∀ m : ZMod 18, cycAdj j m * dftMat m k
      = (if m = j - 1 then psi (m * k) else 0) + (if m = j + 1 then psi (m * k) else 0) := by
    intro m
    rw [cycAdj_apply, dftMat, Matrix.of_apply]
    by_cases h1 : m = j - 1
    · have h2 : m ≠ j + 1 := by rw [h1]; exact sub_one_ne_add_one j
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
    · by_cases h2 : m = j + 1
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
      · rw [if_neg (by tauto), if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl (fun m _ => key m), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun m => psi (m * k)),
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun m => psi (m * k))]
  simp only [Finset.mem_univ, if_true]
  rw [dftMat, eigval, Matrix.of_apply]
  rw [show (j - 1) * k = j * k + -k by ring, show (j + 1) * k = j * k + k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

lemma eigval_eq (k : ZMod 18) :
    eigval k = ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 18) : ℝ) : ℂ) := by
  have hk : (((k.val : ℤ)) : ZMod 18) = k := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  have h1 : psi k = Complex.exp (2 * Real.pi * Complex.I * (k.val : ℤ) / 18) := by
    rw [psi, ← hk, ZMod.stdAddChar_coe]
    norm_num
  have h2 : psi (-k) = Complex.exp (2 * Real.pi * Complex.I * (-(k.val : ℤ)) / 18) := by
    rw [psi, show -k = (((-(k.val : ℤ)) : ℤ) : ZMod 18) by push_cast [hk]; ring,
      ZMod.stdAddChar_coe]
    norm_num
  have h3 : ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 18) : ℝ) : ℂ)
      = 2 * Complex.cos ((2 * Real.pi * (k.val : ℝ) / 18 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [eigval, h1, h2, h3, Complex.two_cos]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

/-- **Hückel theory for `C₁₈`.** The spectrum of the adjacency matrix of the cycle graph
`C₁₈` is exactly the set of numbers `2 cos (2 π k / 18)` for `k = 0, …, 17`. -/
theorem huckel_C18 :
    spectrum ℂ ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : ℕ, k < 18 ∧ μ = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 18) : ℝ) : ℂ)} := by
  have hspec : spectrum ℂ ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) = spectrum ℂ cycAdj := rfl
  rw [hspec]
  set u : (Matrix (ZMod 18) (ZMod 18) ℂ)ˣ := ⟨dftMat, dftInv, dft_mul_inv, inv_mul_dft⟩
  have hconj : cycAdj = (u : Matrix (ZMod 18) (ZMod 18) ℂ) * Matrix.diagonal eigval
      * ((u⁻¹ : (Matrix (ZMod 18) (ZMod 18) ℂ)ˣ) : Matrix (ZMod 18) (ZMod 18) ℂ) := by
    have h : (u : Matrix (ZMod 18) (ZMod 18) ℂ) * Matrix.diagonal eigval = cycAdj * dftMat := by
      rw [adj_mul_dft]
    rw [h]
    show cycAdj = cycAdj * dftMat * dftInv
    rw [Matrix.mul_assoc, dft_mul_inv, Matrix.mul_one]
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  ext μ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, ZMod.val_lt k, eigval_eq k⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ZMod 18), ?_⟩
    rw [eigval_eq, ZMod.val_natCast_of_lt hk]

end Chem

