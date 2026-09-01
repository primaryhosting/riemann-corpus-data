/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the required
-- header above is written as an ordinary block comment; its text is otherwise unchanged.)

import Mathlib

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₈` (the Hückel matrix of cyclooctatetraene,
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`):
vertices `i` and `j` are adjacent iff they are consecutive modulo `8`. -/
def C8adj : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j =>
    if (j : ℕ) = ((i : ℕ) + 1) % 8 ∨ (i : ℕ) = ((j : ℕ) + 1) % 8 then 1 else 0

lemma C8adj_eq :
    C8adj = !![0,1,0,0,0,0,0,1;
                1,0,1,0,0,0,0,0;
                0,1,0,1,0,0,0,0;
                0,0,1,0,1,0,0,0;
                0,0,0,1,0,1,0,0;
                0,0,0,0,1,0,1,0;
                0,0,0,0,0,1,0,1;
                1,0,0,0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C8adj]

lemma C8adj_pow_two :
    C8adj ^ 2 = !![2,0,1,0,0,0,1,0;
                   0,2,0,1,0,0,0,1;
                   1,0,2,0,1,0,0,0;
                   0,1,0,2,0,1,0,0;
                   0,0,1,0,2,0,1,0;
                   0,0,0,1,0,2,0,1;
                   1,0,0,0,1,0,2,0;
                   0,1,0,0,0,1,0,2] := by
  rw [pow_two, C8adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

lemma C8adj_pow_four :
    C8adj ^ 4 = !![6,0,4,0,2,0,4,0;
                   0,6,0,4,0,2,0,4;
                   4,0,6,0,4,0,2,0;
                   0,4,0,6,0,4,0,2;
                   2,0,4,0,6,0,4,0;
                   0,2,0,4,0,6,0,4;
                   4,0,2,0,4,0,6,0;
                   0,4,0,2,0,4,0,6] := by
  have h : C8adj ^ 4 = (C8adj ^ 2) * (C8adj ^ 2) := by ring
  rw [h, C8adj_pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

lemma C8adj_pow_six :
    C8adj ^ 6 = !![20,0,16,0,12,0,16,0;
                   0,20,0,16,0,12,0,16;
                   16,0,20,0,16,0,12,0;
                   0,16,0,20,0,16,0,12;
                   12,0,16,0,20,0,16,0;
                   0,12,0,16,0,20,0,16;
                   16,0,12,0,16,0,20,0;
                   0,16,0,12,0,16,0,20] := by
  have h : C8adj ^ 6 = (C8adj ^ 4) * (C8adj ^ 2) := by ring
  rw [h, C8adj_pow_two, C8adj_pow_four]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

lemma C8adj_pow_eight :
    C8adj ^ 8 = !![72,0,64,0,56,0,64,0;
                   0,72,0,64,0,56,0,64;
                   64,0,72,0,64,0,56,0;
                   0,64,0,72,0,64,0,56;
                   56,0,64,0,72,0,64,0;
                   0,56,0,64,0,72,0,64;
                   64,0,56,0,64,0,72,0;
                   0,64,0,56,0,64,0,72] := by
  have h : C8adj ^ 8 = (C8adj ^ 4) * (C8adj ^ 4) := by ring
  rw [h, C8adj_pow_four]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The characteristic polynomial `X⁸ - 8X⁶ + 20X⁴ - 16X²` annihilates the adjacency matrix. -/
lemma C8adj_annihilating :
    C8adj ^ 8 - (8 : ℝ) • C8adj ^ 6 + (20 : ℝ) • C8adj ^ 4 - (16 : ℝ) • C8adj ^ 2 = 0 := by
  rw [C8adj_pow_two, C8adj_pow_four, C8adj_pow_six, C8adj_pow_eight]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]

lemma mulVec_pow {A : Matrix (Fin 8) (Fin 8) ℝ} {v : Fin 8 → ℝ} {x : ℝ}
    (h : A.mulVec v = x • v) : ∀ n : ℕ, (A ^ n).mulVec v = x ^ n • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, pow_succ, smul_smul,
        mul_comm]

/-- Any eigenvalue of the adjacency matrix is a root of `X⁸ - 8X⁶ + 20X⁴ - 16X²`. -/
lemma eigenvalue_root {x : ℝ} {v : Fin 8 → ℝ} (hv : v ≠ 0) (h : C8adj.mulVec v = x • v) :
    x ^ 8 - 8 * x ^ 6 + 20 * x ^ 4 - 16 * x ^ 2 = 0 := by
  have key : ((x ^ 8 - 8 * x ^ 6 + 20 * x ^ 4 - 16 * x ^ 2) • v) = 0 := by
    have h0 : (C8adj ^ 8 - (8 : ℝ) • C8adj ^ 6 + (20 : ℝ) • C8adj ^ 4
        - (16 : ℝ) • C8adj ^ 2).mulVec v = 0 := by
      rw [C8adj_annihilating]; simp
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc, mulVec_pow h 8, mulVec_pow h 6,
      mulVec_pow h 4, mulVec_pow h 2] at h0
    rw [← h0]
    module
  rcases smul_eq_zero.1 key with h1 | h1
  · exact h1
  · exact absurd h1 hv

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

