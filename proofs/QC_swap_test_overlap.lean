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
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped ComplexConjugate

/-- The tensor (Kronecker) product of two `n`-dimensional pure states, viewed as a vector
indexed by pairs: `(x ⊗ y) (i, j) = x i * y j`. -/
noncomputable def kron {n : ℕ} (x y : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => x p.1 * y p.2)

/-- Inner products factor across tensor products. -/
theorem inner_kron {n : ℕ} (a b c d : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (kron a b) (kron c d) = inner ℂ a c * inner ℂ b d := by
  simp only [kron, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    map_mul, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The acceptance probability of the SWAP test on the input states `x` and `y`.

In the SWAP test the control qubit is measured after a Hadamard–controlled-SWAP–Hadamard
circuit; the outcome `0` ("accept") occurs with probability equal to the squared norm of the
component `½ (x ⊗ y + y ⊗ x)` of the state on the two registers. -/
noncomputable def swapTestAccept {n : ℕ} (x y : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ‖(1 / 2 : ℂ) • (kron x y + kron y x)‖ ^ 2

/-- **Swap test overlap.** For unit vectors (pure states) `x` and `y`, the SWAP test accepts
with probability `(1 + |⟪x, y⟫|²) / 2`. -/
theorem swap_test_overlap {n : ℕ} (x y : EuclideanSpace ℂ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    swapTestAccept x y = (1 + ‖(inner ℂ x y : ℂ)‖ ^ 2) / 2 := by
  set v : EuclideanSpace ℂ (Fin n × Fin n) := (1 / 2 : ℂ) • (kron x y + kron y x) with hv
  have hxx : (inner ℂ x x : ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  have hyy : (inner ℂ y y : ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hy]; norm_num
  have hyx : (inner ℂ y x : ℂ) = conj (inner ℂ x y) := (inner_conj_symm _ _).symm
  have key : (inner ℂ v v : ℂ) = (((1 + ‖(inner ℂ x y : ℂ)‖ ^ 2) / 2 : ℝ) : ℂ) := by
    rw [hv, inner_smul_left, inner_smul_right, inner_add_add_self, inner_kron, inner_kron,
      inner_kron, inner_kron, hxx, hyy, hyx, Complex.mul_conj']
    have hc : conj (inner ℂ x y) * (inner ℂ x y) = ((‖(inner ℂ x y : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj']
    have h2 : conj (1 / 2 : ℂ) = 1 / 2 := by
      simp [Complex.ext_iff]
    rw [h2]
    push_cast
    linear_combination (1 / 4 : ℂ) * hc
  rw [inner_self_eq_norm_sq_to_K] at key
  have : ((‖v‖ ^ 2 : ℝ) : ℂ) = (((1 + ‖(inner ℂ x y : ℂ)‖ ^ 2) / 2 : ℝ) : ℂ) := by
    push_cast; push_cast at key; exact key
  exact_mod_cast this

end QC

