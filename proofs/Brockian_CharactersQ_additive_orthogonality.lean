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

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Tactic

/-!
# Fourier analysis and characters on `ZMod q`

The reusable, general-modulus character kernel needed by the analytic large-sieve and
Bombieri--Vinogradov layers.  This module deliberately wraps Mathlib's canonical
`ZMod.stdAddChar`, `ZMod.dft`, and `DirichletCharacter`; it introduces no competing
character convention.
-/

open scoped BigOperators

noncomputable section

namespace Brockian.CharactersQ

variable (q : ℕ) [NeZero q]

/-- Mathlib's canonical additive character `x ↦ exp (2πix/q)`. -/
abbrev additiveChar : AddChar (ZMod q) ℂ := ZMod.stdAddChar

/-- Complex Dirichlet characters modulo `q`, reused from Mathlib. -/
abbrev MultiplicativeChar := DirichletCharacter ℂ q

/-- The unnormalised discrete Fourier transform on `ZMod q`. -/
noncomputable def fourier (f : ZMod q → ℂ) : ZMod q → ℂ := ZMod.dft f

@[simp] theorem fourier_apply (f : ZMod q → ℂ) (a : ZMod q) :
    fourier q f a = ∑ x : ZMod q, additiveChar q (-(x * a)) * f x := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]

/-- Additive-character orthogonality on `ZMod q`. -/
theorem additive_orthogonality (a : ZMod q) :
    ∑ x : ZMod q, additiveChar q (x * a) = if a = 0 then (q : ℂ) else 0 := by
  simpa [additiveChar, ZMod.card] using
    (AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod q) ℂ)) a
      (ZMod.isPrimitive_stdAddChar q))

/-- Delta-function form of additive-character orthogonality. -/
theorem additive_orthogonality_sub (x y : ZMod q) :
    ∑ a : ZMod q, additiveChar q (a * (x - y)) = if x = y then (q : ℂ) else 0 := by
  rw [additive_orthogonality]
  simp only [sub_eq_zero]

/-- Applying the unnormalised transform twice reflects the input and multiplies by `q`. -/
theorem fourier_twice (f : ZMod q → ℂ) :
    fourier q (fourier q f) = fun x ↦ (q : ℂ) * f (-x) := by
  simpa only [fourier, smul_eq_mul] using (ZMod.dft_dft f)

/-- Exact Fourier inversion on `ZMod q`. -/
theorem fourier_inversion (f : ZMod q → ℂ) (x : ZMod q) :
    f x = (q : ℂ)⁻¹ *
      ∑ a : ZMod q, additiveChar q (a * x) * fourier q f a := by
  calc
    f x = (ZMod.dft.symm (ZMod.dft f)) x := by simp
    _ = (q : ℂ)⁻¹ *
        ∑ a : ZMod q, additiveChar q (a * x) * fourier q f a := by
      simp only [ZMod.invDFT_apply, additiveChar, fourier, smul_eq_mul]

private theorem conj_additiveChar (x : ZMod q) :
    (starRingEnd ℂ) (additiveChar q x) = additiveChar q (-x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
  simp [← Circle.coe_inv_eq_conj]

/-- Complex-valued core of Parseval's identity. -/
private theorem parseval_core (f : ZMod q → ℂ) :
    ∑ a : ZMod q, fourier q f a * (starRingEnd ℂ) (fourier q f a) =
      (q : ℂ) * ∑ x : ZMod q, f x * (starRingEnd ℂ) (f x) := by
  have hexp : ∀ a : ZMod q,
      fourier q f a * (starRingEnd ℂ) (fourier q f a) =
        ∑ x : ZMod q, ∑ y : ZMod q,
          f x * (starRingEnd ℂ) (f y) * additiveChar q (a * (y - x)) := by
    intro a
    rw [fourier_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    have key : additiveChar q (-(x * a)) * additiveChar q (- -(y * a)) =
        additiveChar q (a * (y - x)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [map_mul, conj_additiveChar]
    linear_combination (f x * (starRingEnd ℂ) (f y)) * key
  rw [Finset.sum_congr rfl (fun a _ => hexp a)]
  rw [Finset.sum_comm]
  have hdiag : ∀ x : ZMod q,
      ∑ a : ZMod q, ∑ y : ZMod q,
          f x * (starRingEnd ℂ) (f y) * additiveChar q (a * (y - x)) =
        (q : ℂ) * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have hin : ∀ y : ZMod q,
        ∑ a : ZMod q,
            f x * (starRingEnd ℂ) (f y) * additiveChar q (a * (y - x)) =
          if y = x then (q : ℂ) * (f x * (starRingEnd ℂ) (f y)) else 0 := by
      intro y
      rw [← Finset.mul_sum]
      rw [additive_orthogonality_sub]
      by_cases h : y = x
      · subst h
        simp [mul_comm]
      · simp [h]
    rw [Finset.sum_congr rfl (fun y _ => hin y), Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [Finset.sum_congr rfl (fun x _ => hdiag x), ← Finset.mul_sum]

/-- Parseval/Plancherel for the unnormalised DFT on every nonzero modulus. -/
theorem parseval (f : ZMod q → ℂ) :
    ∑ a : ZMod q, ‖fourier q f a‖ ^ 2 =
      q * ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have h := parseval_core q f
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have hcast :
      (((∑ a : ZMod q, ‖fourier q f a‖ ^ 2 : ℝ)) : ℂ) =
        (((q * ∑ x : ZMod q, ‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  exact_mod_cast hcast

/-- A nontrivial complex Dirichlet character has zero complete sum. -/
theorem multiplicative_orthogonality (χ : MultiplicativeChar q) (hχ : χ ≠ 1) :
    ∑ x : ZMod q, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

/-- The unnormalised DFT is bounded by the `ℓ¹` norm of the input. -/
theorem norm_fourier_le_sum_norm (f : ZMod q → ℂ) (x : ZMod q) :
    ‖fourier q f x‖ ≤ ∑ y : ZMod q, ‖f y‖ := by
  rw [fourier_apply]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
  rw [norm_mul, additiveChar, ZMod.stdAddChar_apply]
  simp

end Brockian.CharactersQ

