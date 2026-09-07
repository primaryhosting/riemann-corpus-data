/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex Real ZMod AddChar

namespace QC

/-- The `N × N` quantum Fourier transform matrix, indexed by `ZMod N`:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun j k => Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / N) / Real.sqrt N

/-- The entries of the QFT matrix in terms of the standard additive character of `ZMod N`. -/
lemma qftMatrix_apply (N : ℕ) [NeZero N] (j k : ZMod N) :
    qftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (j * k) := by
  have h : ((j.val * k.val : ℕ) : ZMod N) = j * k := by push_cast [ZMod.natCast_val]; simp
  rw [qftMatrix]
  simp only [Matrix.of_apply]
  rw [div_eq_inv_mul, ← h,
    show ((j.val * k.val : ℕ) : ZMod N) = (((j.val * k.val : ℕ) : ℤ) : ZMod N) by push_cast; ring,
    ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- Complex conjugation inverts the standard additive character. -/
lemma conj_stdAddChar (N : ℕ) [NeZero N] (x : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.starComp_apply (by simp [ZMod.ringChar_zmod_n, Nat.pos_of_neZero]), AddChar.inv_apply]

/-- Orthogonality relation: the character sum `∑ k, ζ^(k t)` is `N` if `t = 0` and `0` otherwise. -/
lemma sum_stdAddChar (N : ℕ) [NeZero N] (t : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (k * t) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · simpa [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- The `N`-dimensional quantum Fourier transform matrix is unitary. -/
theorem qftMatrix_unitary (N : ℕ) [NeZero N] :
    qftMatrix N ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_neZero N)
  have hsq : ((Real.sqrt N : ℂ)) * ((Real.sqrt N : ℂ)) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le]; simp
  have hne : ((Real.sqrt N : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, Real.sqrt_eq_zero', not_le]
    exact hN
  have hs : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ * (N : ℂ) = 1 := by
    rw [← hsq]; field_simp
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod N, (star (qftMatrix N)) j k * qftMatrix N k l
      = (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (k * (l - j)) := by
    intro k
    have h1 : (starRingEnd ℂ) ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ := by simp
    have hchar : ZMod.stdAddChar (-(k * j)) * ZMod.stdAddChar (k * l)
        = ZMod.stdAddChar (k * (l - j)) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [Matrix.star_apply, RCLike.star_def, qftMatrix_apply, qftMatrix_apply, map_mul,
      conj_stdAddChar, h1, ← hchar]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_stdAddChar]
  rcases eq_or_ne j l with h | h
  · simp [h, hs, Matrix.one_apply]
  · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using h)]
    simp [h]

/-- The 8-qubit quantum Fourier transform matrix (of size `2^8 = 256`) is unitary. -/
theorem qft_unitary_8 : qftMatrix (2 ^ 8) ∈ Matrix.unitaryGroup (ZMod (2 ^ 8)) ℂ :=
  qftMatrix_unitary _

end QC

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

