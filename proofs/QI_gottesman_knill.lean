/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace QI

open Matrix

/-! ## Bit strings -/

/-- Bit strings of length `n`; `Bits n` indexes the computational basis of `n` qubits. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- Bitwise xor of two bit strings. -/
def bxor {n : ℕ} (u v : Bits n) : Bits n := fun j => xor (u j) (v j)

/-- The all-zero bit string. -/
def bzero (n : ℕ) : Bits n := fun _ => false

/-- The bit string with a single `1` in position `k`. -/
def unitb {n : ℕ} (k : Fin n) : Bits n := fun j => decide (j = k)

/-- `bsgn a b = (-1) ^ ⟪a, b⟫` where `⟪a,b⟫ = ∑ j, a j * b j`. -/
def bsgn {n : ℕ} (a b : Bits n) : ℂ := ∏ j, if a j && b j then (-1 : ℂ) else 1

@[simp] lemma bxor_self {n : ℕ} (u : Bits n) : bxor u u = bzero n := by
  funext j; simp [bxor, bzero]

@[simp] lemma bxor_zero {n : ℕ} (u : Bits n) : bxor u (bzero n) = u := by
  funext j; simp [bxor, bzero]

@[simp] lemma zero_bxor {n : ℕ} (u : Bits n) : bxor (bzero n) u = u := by
  funext j; simp [bxor, bzero]

lemma bxor_comm {n : ℕ} (u v : Bits n) : bxor u v = bxor v u := by
  funext j; simp [bxor, Bool.xor_comm]

lemma bxor_assoc {n : ℕ} (u v w : Bits n) : bxor (bxor u v) w = bxor u (bxor v w) := by
  funext j; simp [bxor]

@[simp] lemma bxor_cancel {n : ℕ} (u v : Bits n) : bxor (bxor u v) v = u := by
  rw [bxor_assoc, bxor_self, bxor_zero]

@[simp] lemma bxor_cancel' {n : ℕ} (u v : Bits n) : bxor u (bxor u v) = v := by
  rw [← bxor_assoc, bxor_self, zero_bxor]

@[simp] lemma bxor_apply {n : ℕ} (u v : Bits n) (j : Fin n) : bxor u v j = xor (u j) (v j) := rfl

@[simp] lemma bzero_apply {n : ℕ} (j : Fin n) : bzero n j = false := rfl

@[simp] lemma unitb_apply_self {n : ℕ} (k : Fin n) : unitb k k = true := by simp [unitb]

lemma bsgn_bxor_right {n : ℕ} (a b c : Bits n) : bsgn a (bxor b c) = bsgn a b * bsgn a c := by
  simp only [bsgn, bxor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain hA | hA := Bool.eq_false_or_eq_true (a j) <;>
    obtain hB | hB := Bool.eq_false_or_eq_true (b j) <;>
      obtain hC | hC := Bool.eq_false_or_eq_true (c j) <;> simp [hA, hB, hC]

lemma bsgn_bxor_left {n : ℕ} (a b c : Bits n) : bsgn (bxor a b) c = bsgn a c * bsgn b c := by
  simp only [bsgn, bxor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain hA | hA := Bool.eq_false_or_eq_true (a j) <;>
    obtain hB | hB := Bool.eq_false_or_eq_true (b j) <;>
      obtain hC | hC := Bool.eq_false_or_eq_true (c j) <;> simp [hA, hB, hC]

@[simp] lemma bsgn_zero_left {n : ℕ} (b : Bits n) : bsgn (bzero n) b = 1 := by
  simp [bsgn, bzero]

@[simp] lemma bsgn_zero_right {n : ℕ} (a : Bits n) : bsgn a (bzero n) = 1 := by
  simp [bsgn, bzero]

lemma bsgn_comm {n : ℕ} (a b : Bits n) : bsgn a b = bsgn b a := by
  simp only [bsgn]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain hA | hA := Bool.eq_false_or_eq_true (a j) <;>
    obtain hB | hB := Bool.eq_false_or_eq_true (b j) <;> simp [hA, hB]

lemma bsgn_unitb_left {n : ℕ} (k : Fin n) (v : Bits n) :
    bsgn (unitb k) v = if v k then -1 else 1 := by
  simp only [bsgn]
  rw [Finset.prod_eq_single k]
  · simp [unitb]
  · intro j _ hj; simp [unitb, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma bsgn_unitb_right {n : ℕ} (k : Fin n) (v : Bits n) :
    bsgn v (unitb k) = if v k then -1 else 1 := by
  rw [bsgn_comm, bsgn_unitb_left]

lemma bsgn_star {n : ℕ} (a b : Bits n) : star (bsgn a b) = bsgn a b := by
  show (starRingEnd ℂ) (bsgn a b) = bsgn a b
  simp only [bsgn, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain hA | hA := Bool.eq_false_or_eq_true (a j) <;>
    obtain hB | hB := Bool.eq_false_or_eq_true (b j) <;> simp [hA, hB]

lemma bsgn_sq {n : ℕ} (a b : Bits n) : bsgn a b * bsgn a b = 1 := by
  simp only [bsgn, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  obtain hA | hA := Bool.eq_false_or_eq_true (a j) <;>
    obtain hB | hB := Bool.eq_false_or_eq_true (b j) <;> simp [hA, hB]

lemma update_eq_bxor_unitb {n : ℕ} (x : Bits n) (k : Fin n) (b : Bool) (h : b = !(x k)) :
    Function.update x k b = bxor x (unitb k) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [h, Function.update_self]
  · simp [unitb, hj]

lemma update_eq_self' {n : ℕ} (x : Bits n) (k : Fin n) (b : Bool) (h : b = x k) :
    Function.update x k b = x := by
  subst h; exact Function.update_eq_self k x

/-! ## Pauli operators as matrices -/

/-- `Pmat x z` is the Pauli operator `X^x Z^z` acting on `n` qubits:
it maps the computational basis vector `|v⟩` to `(-1)^{z·v} |v ⊕ x⟩`. -/
def Pmat {n : ℕ} (x z : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun u v => if u = bxor v x then bsgn z v else 0

@[simp] lemma Pmat_apply {n : ℕ} (x z u v : Bits n) :
    Pmat x z u v = if u = bxor v x then bsgn z v else 0 := rfl

@[simp] lemma Pmat_zero {n : ℕ} : Pmat (bzero n) (bzero n) = 1 := by
  ext u v
  simp [Pmat, Matrix.one_apply]

/-- Multiplication rule for Pauli operators. -/
lemma pmul {n : ℕ} (x1 z1 x2 z2 : Bits n) :
    Pmat x1 z1 * Pmat x2 z2 = bsgn z1 x2 • Pmat (bxor x1 x2) (bxor z1 z2) := by
  ext u v
  rw [Matrix.mul_apply, Finset.sum_eq_single (bxor v x2)]
  · have hcond : bxor (bxor v x2) x1 = bxor v (bxor x1 x2) := by
      rw [bxor_assoc, bxor_comm x2 x1]
    simp only [Pmat_apply, Matrix.smul_apply, smul_eq_mul, hcond, if_true]
    by_cases h : u = bxor v (bxor x1 x2)
    · rw [if_pos h, if_pos h, bsgn_bxor_right, bsgn_bxor_left]; ring
    · rw [if_neg h, if_neg h]; ring
  · intro w _ hw
    simp only [Pmat_apply]
    rw [if_neg hw, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Pmat_conjTranspose {n : ℕ} (x z : Bits n) :
    (Pmat x z)ᴴ = bsgn z x • Pmat x z := by
  ext u v
  simp only [Matrix.conjTranspose_apply, Pmat_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : u = bxor v x
  · have h' : v = bxor u x := by rw [h, bxor_cancel]
    rw [if_pos h, if_pos h', bsgn_star, h, bsgn_bxor_right]
    ring
  · have h' : ¬ v = bxor u x := by
      intro hv; exact h (by rw [hv, bxor_cancel])
    rw [if_neg h, if_neg h', star_zero, mul_zero]

end QI

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

