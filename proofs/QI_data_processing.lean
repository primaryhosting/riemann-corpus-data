/-
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

open Matrix Finset

/-! ## Classical relative entropy (Kullback-Leibler divergence) -/

/-- The Kullback-Leibler divergence of two finitely supported "distributions". -/
noncomputable def klDiv {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- `1 - 1/x ≤ log x` for positive `x`. -/
lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := x⁻¹) (by positivity)
  rw [Real.log_inv] at h
  linarith

/-- The log-sum inequality. -/
theorem log_sum_inequality {α : Type*} [Fintype α] (a b : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hB0 with hBz | hBpos
  · -- `B = 0` forces all `b i = 0`, hence all `a i = 0`
    have hbz : ∀ i, b i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hb j)).1 (hB.symm.trans hBz.symm) i
        (Finset.mem_univ i)
    have haz : ∀ i, a i = 0 := fun i => hab i (hbz i)
    have hAz : A = 0 := by simp [hA, haz]
    simp [hAz, haz]
  · rcases eq_or_lt_of_le hA0 with hAz | hApos
    · have haz : ∀ i, a i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 hAz.symm i (Finset.mem_univ i)
      simp [haz, ← hAz]
    · have key : ∀ i, a i - b i * (A / B) ≤ a i * (Real.log (a i / b i) - Real.log (A / B)) := by
        intro i
        rcases eq_or_lt_of_le (ha i) with hai | hai
        · have hbA : 0 ≤ b i * (A / B) := mul_nonneg (hb i) (div_nonneg hA0 hB0)
          rw [← hai]
          simp only [zero_mul, zero_sub]
          linarith
        · have hbi : 0 < b i := by
            rcases eq_or_lt_of_le (hb i) with h | h
            · exact absurd (hab i h.symm) (by linarith)
            · exact h
          have hx : 0 < (a i / b i) / (A / B) := by positivity
          have hlog : Real.log ((a i / b i) / (A / B)) =
              Real.log (a i / b i) - Real.log (A / B) :=
            Real.log_div (by positivity) (by positivity)
          rw [← hlog]
          have h1 := one_sub_inv_le_log hx
          have h2 : a i * (1 - ((a i / b i) / (A / B))⁻¹) ≤
              a i * Real.log ((a i / b i) / (A / B)) := by
            exact mul_le_mul_of_nonneg_left h1 (le_of_lt hai)
          refine le_trans (le_of_eq ?_) h2
          field_simp
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
      rw [Finset.sum_sub_distrib] at hsum
      simp only [← Finset.sum_mul, ← hA, ← hB] at hsum
      have hBB : B * (A / B) = A := by field_simp
      rw [hBB] at hsum
      have : ∑ i, a i * (Real.log (a i / b i) - Real.log (A / B))
          = (∑ i, a i * Real.log (a i / b i)) - A * Real.log (A / B) := by
        rw [Finset.sum_congr rfl (fun i _ => mul_sub (a i) _ _), Finset.sum_sub_distrib,
          ← Finset.sum_mul, ← hA]
      rw [this] at hsum
      linarith

/-- Classical data-processing inequality: the KL divergence does not increase under the
action of a (column-)stochastic matrix. -/
theorem klDiv_stochastic_le {α β : Type*} [Fintype α] [Fintype β]
    (T : β → α → ℝ) (hT0 : ∀ k i, 0 ≤ T k i) (hT1 : ∀ i, ∑ k, T k i = 1)
    (p q : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    klDiv (fun k => ∑ i, T k i * p i) (fun k => ∑ i, T k i * q i) ≤ klDiv p q := by
  have step1 : ∀ k, (∑ i, T k i * p i) * Real.log ((∑ i, T k i * p i) / (∑ i, T k i * q i))
      ≤ ∑ i, (T k i * p i) * Real.log ((T k i * p i) / (T k i * q i)) := by
    intro k
    refine log_sum_inequality _ _ (fun i => mul_nonneg (hT0 k i) (hp i))
      (fun i => mul_nonneg (hT0 k i) (hq i).le) (fun i h => ?_)
    rcases mul_eq_zero.1 h with h' | h'
    · simp [h']
    · exact absurd h' (ne_of_gt (hq i))
  have step2 : ∀ k i, (T k i * p i) * Real.log ((T k i * p i) / (T k i * q i))
      = T k i * (p i * Real.log (p i / q i)) := by
    intro k i
    rcases eq_or_lt_of_le (hT0 k i) with h | h
    · simp [← h]
    · rw [mul_div_mul_left _ _ (ne_of_gt h)]; ring
  have step3 : ∀ k, (∑ i, T k i * p i) * Real.log ((∑ i, T k i * p i) / (∑ i, T k i * q i))
      ≤ ∑ i, T k i * (p i * Real.log (p i / q i)) := by
    intro k
    refine le_trans (step1 k) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => step2 k i
  refine le_trans (Finset.sum_le_sum fun k _ => step3 k) (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, hT1 i, one_mul]

/-- Nonnegativity of the classical relative entropy of two probability vectors. -/
theorem klDiv_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    0 ≤ klDiv p q := by
  have h := log_sum_inequality p q (fun i => hp i) (fun i => (hq i).le)
    (fun i h => absurd h (ne_of_gt (hq i)))
  rw [hp1, hq1] at h
  simpa [klDiv] using h

/-! ## Quantum relative entropy -/

section Quantum

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Umegaki relative entropy `Tr ρ (log ρ - log σ)` of two density matrices,
the matrix logarithm being given by the continuous functional calculus. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * cfc Real.log ρ)).re - (Matrix.trace (ρ * cfc Real.log σ)).re

/-- The probability of the `i`-th outcome when the projective measurement in the eigenbasis of
the Hermitian matrix `A` (the eigenbasis provided by the spectral theorem) is performed on the
state `X`. -/
noncomputable def eigenMeasure {A : Matrix n n ℂ} (hA : A.IsHermitian) (X : Matrix n n ℂ)
    (i : n) : ℝ :=
  ((star (hA.eigenvectorUnitary : Matrix n n ℂ) * X * (hA.eigenvectorUnitary : Matrix n n ℂ))
    i i).re

/-- A convex combination of positive numbers is positive. -/
lemma pos_of_convex_comb {α : Type*} [Fintype α] (w q : α → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (hq : ∀ j, 0 < q j) : 0 < ∑ j, w j * q j := by
  have hnn : 0 ≤ ∑ j, w j * q j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw0 j) (hq j).le
  rcases eq_or_lt_of_le hnn with hz | hs
  · exfalso
    have hz' : ∀ j ∈ Finset.univ, w j * q j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hw0 j) (hq j).le).1 hz.symm
    have hw : ∀ j, w j = 0 := by
      intro j
      rcases mul_eq_zero.1 (hz' j (Finset.mem_univ j)) with h | h
      · exact h
      · exact absurd h (ne_of_gt (hq j))
    rw [Finset.sum_congr rfl fun j _ => hw j] at hw1
    simp at hw1
  · exact hs

/-- Jensen's inequality for `Real.log` and a finite convex combination. -/
lemma sum_log_le_log_sum {α : Type*} [Fintype α] (w q : α → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (hq : ∀ j, 0 < q j) :
    ∑ j, w j * Real.log (q j) ≤ Real.log (∑ j, w j * q j) := by
  have hs : 0 < ∑ j, w j * q j := pos_of_convex_comb w q hw0 hw1 hq
  set S := ∑ j, w j * q j with hS
  have key : ∀ j, w j * Real.log (q j) - w j * Real.log S ≤ w j * (q j / S) - w j := by
    intro j
    have h1 : Real.log (q j / S) ≤ q j / S - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hq j) hs)
    have h2 : Real.log (q j / S) = Real.log (q j) - Real.log S :=
      Real.log_div (ne_of_gt (hq j)) (ne_of_gt hs)
    have h3 := mul_le_mul_of_nonneg_left h1 (hw0 j)
    rw [h2] at h3
    nlinarith [h3]
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul,
    ] at hsum
  have hone : ∑ j, w j * (q j / S) = 1 := by
    have : ∑ j, w j * (q j / S) = (∑ j, w j * q j) / S := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, ← hS, div_self (ne_of_gt hs)]
  rw [hone] at hsum
  linarith

omit [DecidableEq n] in
/-- The core inequality: relative entropy dominates the classical relative entropy of the
measurement statistics, in a purely real-valued formulation. -/
lemma klDiv_le_of_doublyStochastic {p q : n → ℝ} {W : n → n → ℝ}
    (hW0 : ∀ i j, 0 ≤ W i j) (hWrow : ∀ i, ∑ j, W i j = 1)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 < q j) :
    klDiv p (fun i => ∑ j, W i j * q j)
      ≤ (∑ i, p i * Real.log (p i)) - ∑ j, (∑ i, W i j * p i) * Real.log (q j) := by
  have hs : ∀ i, 0 < ∑ j, W i j * q j :=
    fun i => pos_of_convex_comb _ q (fun j => hW0 i j) (hWrow i) hq
  have jensen : ∀ i, p i * ∑ j, W i j * Real.log (q j) ≤ p i * Real.log (∑ j, W i j * q j) :=
    fun i => mul_le_mul_of_nonneg_left
      (sum_log_le_log_sum _ _ (fun j => hW0 i j) (hWrow i) hq) (hp i)
  have swap : ∑ j, (∑ i, W i j * p i) * Real.log (q j)
      = ∑ i, p i * ∑ j, W i j * Real.log (q j) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have lhs_eq : klDiv p (fun i => ∑ j, W i j * q j)
      = ∑ i, (p i * Real.log (p i) - p i * Real.log (∑ j, W i j * q j)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_lt_of_le (hp i) with h | h
    · simp [← h]
    · rw [Real.log_div (ne_of_gt h) (ne_of_gt (hs i))]; ring
  rw [lhs_eq, Finset.sum_sub_distrib, swap]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => jensen i
  linarith

/-! ### Spectral computations -/

/-- Diagonalization of a Hermitian matrix by its eigenvector unitary. -/
lemma star_mul_mul_eigenvectorUnitary {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix n n ℂ) * A * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  simpa [Function.comp_def] using h

/-- Diagonal entries of a matrix conjugated with a real diagonal matrix. -/
lemma mul_diagonal_mul_star_apply (N : Matrix n n ℂ) (d : n → ℝ) (i : n) :
    (N * Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) * star N) i i
      = ((∑ j, Complex.normSq (N i j) * d j : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, Complex.normSq_eq_conj_mul_self]
    simp [RCLike.star_def]
    ring
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Diagonal entries of a matrix conjugated (the other way) with a real diagonal matrix. -/
lemma star_mul_diagonal_mul_apply (N : Matrix n n ℂ) (d : n → ℝ) (j : n) :
    (star N * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * N) j j
      = ((∑ i, Complex.normSq (N i j) * d i : ℝ) : ℂ) := by
  have h := mul_diagonal_mul_star_apply (star N) d j
  rw [star_star] at h
  rw [h]
  norm_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.star_apply, Complex.normSq_conj]

/-- The trace of a product with a diagonal matrix. -/
lemma trace_mul_diagonal (M : Matrix n n ℂ) (d : n → ℂ) :
    Matrix.trace (M * Matrix.diagonal d) = ∑ j, M j j * d j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

/-- Trace of a matrix against the logarithm of a Hermitian matrix, in the latter's eigenbasis. -/
lemma trace_mul_cfc_log {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n n ℂ) :
    Matrix.trace (B * cfc Real.log A)
      = ∑ j, ((star (hA.eigenvectorUnitary : Matrix n n ℂ) * B *
          (hA.eigenvectorUnitary : Matrix n n ℂ)) j j)
            * ((Real.log (hA.eigenvalues j) : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := Matrix.diagonal (fun j => ((Real.log (hA.eigenvalues j) : ℝ) : ℂ))
    with hD
  have h1 : cfc Real.log A = U * D * star U := by
    rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  have h2 : B * (U * D * star U) = B * U * D * star U := by simp only [Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_cycle (B * U) D (star U)]
  have h3 : star U * (B * U) * D = star U * B * U * D := by simp only [Matrix.mul_assoc]
  rw [h3, hD, trace_mul_diagonal]

/-- The rows of a unitary matrix have unit length. -/
lemma sum_normSq_row {M : Matrix n n ℂ} (hM : M ∈ Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, Complex.normSq (M i j) = 1 := by
  have h : M * star M = 1 := Unitary.mul_star_self_of_mem hM
  have h2 := congrArg (fun X : Matrix n n ℂ => X i i) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h2
  have h3 : ((∑ j, Complex.normSq (M i j) : ℝ) : ℂ) = 1 := by
    rw [← h2]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [RCLike.star_def]
    ring
  exact_mod_cast h3

/-- The columns of a unitary matrix have unit length. -/
lemma sum_normSq_col {M : Matrix n n ℂ} (hM : M ∈ Matrix.unitaryGroup n ℂ) (j : n) :
    ∑ i, Complex.normSq (M i j) = 1 := by
  have hM' : star M ∈ Matrix.unitaryGroup n ℂ := Unitary.star_mem hM
  have h := sum_normSq_row hM' j
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.star_apply, Complex.normSq_conj]

end Quantum

end QI

