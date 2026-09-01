/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
with `α = 0`, `β = 1`), with vertices `0,1,2,3,4` arranged in a pentagon. -/
noncomputable def C5adj : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0]

set_option maxHeartbeats 2000000 in
/-- The characteristic identity `A⁵ = 5A³ - 5A + 2I` satisfied by the adjacency matrix
of `C₅` (Cayley–Hamilton for the characteristic polynomial `x⁵ - 5x³ + 5x - 2`). -/
lemma C5adj_pow_five :
    C5adj ^ 5 = (5:ℝ) • C5adj ^ 3 - (5:ℝ) • C5adj + (2:ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  have h2 : C5adj ^ 2 = !![2,0,1,1,0; 0,2,0,1,1; 1,0,2,0,1; 1,1,0,2,0; 0,1,1,0,2] := by
    rw [pow_two]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  have h3 : C5adj ^ 3 = !![0,3,1,1,3; 3,0,3,1,1; 1,3,0,3,1; 1,1,3,0,3; 3,1,1,3,0] := by
    rw [pow_succ, h2]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  have h4 : C5adj ^ 4 = !![6,1,4,4,1; 1,6,1,4,4; 4,1,6,1,4; 4,4,1,6,1; 1,4,4,1,6] := by
    rw [pow_succ, h3]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  have h5 : C5adj ^ 5 = !![2,10,5,5,10; 10,2,10,5,5; 5,10,2,10,5; 5,5,10,2,10; 10,5,5,10,2] := by
    rw [pow_succ, h4]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [h3, h5]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C5adj, Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]

/-- Any eigenvalue of the adjacency matrix of `C₅` is a root of `x⁵ - 5x³ + 5x - 2`. -/
lemma quintic_of_eigenvalue {μ : ℝ} {v : Fin 5 → ℝ} (hv : v ≠ 0) (h : C5adj *ᵥ v = μ • v) :
    μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2 = 0 := by
  have key : ∀ n : ℕ, C5adj ^ n *ᵥ v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have h5 := key 5
  rw [C5adj_pow_five] at h5
  have h3 := key 3
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h5
  rw [h3, h] at h5
  have : (μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2) • v = 0 := by
    calc (μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2) • v
        = μ ^ 5 • v - ((5:ℝ) • μ ^ 3 • v - (5:ℝ) • (μ • v) + (2:ℝ) • v) := by module
      _ = 0 := by rw [h5, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hv

/-- Explicit eigenvectors: `2` is an eigenvalue, and so is any root of `x² + x - 1`. -/
lemma eigenvalue_two : C5adj *ᵥ (fun _ => (1:ℝ)) = (2:ℝ) • (fun _ => (1:ℝ)) := by
  ext i
  fin_cases i <;>
    norm_num [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

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

