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

open Finset

-- Everything lives in this namespace so that `fourier` refers to the discrete Fourier
-- transform defined below rather than to Mathlib's `fourier` on `AddCircle`.
namespace CharacterSums

variable {q : ℕ} [NeZero q]

/-- The (unnormalised) discrete Fourier transform on `ZMod q`. -/
noncomputable def fourier (f : ZMod q → ℂ) : ZMod q → ℂ := ZMod.dft f

@[simp] theorem fourier_apply (f : ZMod q → ℂ) (a : ZMod q) :
    fourier f a = ∑ x : ZMod q, ZMod.stdAddChar (-(x * a)) * f x := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]

/-- Fourier inversion. Note the normalising factor `(q : ℂ)⁻¹`: `fourier f 0 = ∑ x, f x` is
`q` times the mean of `f`, not the mean itself. -/
theorem fourier_inversion (f : ZMod q → ℂ) (x : ZMod q) :
    f x = (q : ℂ)⁻¹ * ∑ a : ZMod q, ZMod.stdAddChar (a * x) * fourier f a := by
  calc
    f x = (ZMod.dft.symm (ZMod.dft f)) x := by simp
    _ = (q : ℂ)⁻¹ * ∑ a : ZMod q, ZMod.stdAddChar (a * x) * fourier f a := by
        simp only [ZMod.invDFT_apply, fourier, smul_eq_mul]

theorem norm_stdAddChar (x : ZMod q) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem card_erase_zero : (univ.erase (0 : ZMod q)).card = (q - 1 : ℕ) := by
  rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card]

/-- The mean of `f` is `(q : ℂ)⁻¹ * fourier f 0`, and the deviation of `f` from its mean at
any point is controlled by the nonzero Fourier coefficients, with the sharp constant
`(q - 1) / q`. -/
theorem sub_mean_le_of_fourier_bound_sharp (f : ZMod q → ℂ) (B : ℝ)
    (hB : ∀ k : ZMod q, k ≠ 0 → ‖fourier f k‖ ≤ B) (x : ZMod q) :
    ‖f x - (q : ℂ)⁻¹ * fourier f 0‖ ≤ (q : ℝ)⁻¹ * ((q - 1 : ℕ) * B) := by
  have hsplit : ∑ a : ZMod q, ZMod.stdAddChar (a * x) * fourier f a
      = fourier f 0 + ∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod q))]
    simp
  have hkey : f x - (q : ℂ)⁻¹ * fourier f 0
      = (q : ℂ)⁻¹ * ∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a := by
    rw [fourier_inversion f x, hsplit, mul_add]
    ring
  have hsum : ‖∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a‖
      ≤ (q - 1 : ℕ) * B := by
    calc ‖∑ a ∈ univ.erase (0 : ZMod q), ZMod.stdAddChar (a * x) * fourier f a‖
        ≤ ∑ a ∈ univ.erase (0 : ZMod q), ‖ZMod.stdAddChar (a * x) * fourier f a‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _a ∈ univ.erase (0 : ZMod q), B := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [norm_mul, norm_stdAddChar, one_mul]
          exact hB a (Finset.ne_of_mem_erase ha)
      _ = (q - 1 : ℕ) * B := by
          rw [Finset.sum_const, card_erase_zero, nsmul_eq_mul]
  rw [hkey, norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/--
The statement originally requested,

```
theorem sub_mean_le_of_fourier_bound {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (B : ℝ) (hB : ∀ k : ZMod q, k ≠ 0 → ‖fourier f k‖ ≤ B)
    (x : ZMod q) :
    ‖f x - fourier f 0‖ ≤ (q - 1 : ℕ) * B
```

is **false** with the corpus definition `fourier f = ZMod.dft f`, which is the *unnormalised*
transform: `fourier f 0 = ∑ x, f x` equals `q` times the mean of `f`, not the mean.
For `q = 2` and `f` the constant function `1` all nonzero Fourier coefficients vanish, so the
hypothesis holds with `B = 0`, while `‖f 0 - fourier f 0‖ = ‖1 - 2‖ = 1 > 0`.
This theorem records that refutation; the corrected statements, with the mean
`(q : ℂ)⁻¹ * fourier f 0` in place of `fourier f 0`, are
`sub_mean_le_of_fourier_bound_sharp` and `sub_mean_le_of_fourier_bound`.
-/
theorem not_sub_dft_zero_le_of_fourier_bound :
    ¬ ∀ (q : ℕ) [NeZero q] (f : ZMod q → ℂ) (B : ℝ),
        (∀ k : ZMod q, k ≠ 0 → ‖fourier f k‖ ≤ B) → ∀ x : ZMod q,
          ‖f x - fourier f 0‖ ≤ (q - 1 : ℕ) * B := by
  intro h
  have hchar : (ZMod.stdAddChar (1 : ZMod 2)) = -1 := by
    have h2 := ZMod.stdAddChar_coe (N := 2) 1
    push_cast at h2
    rw [h2, show (2 * Real.pi * Complex.I * 1 / 2) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have hu : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  set f : ZMod 2 → ℂ := fun _ => 1 with hf
  have hB : ∀ k : ZMod 2, k ≠ 0 → ‖fourier f k‖ ≤ 0 := by
    intro k hk
    have hk1 : k = 1 := by revert hk; revert k; decide
    subst hk1
    have : fourier f (1 : ZMod 2) = 0 := by
      rw [fourier_apply]
      rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
      norm_num [hf]
      rw [show (-(1 : ZMod 2)) = 1 by decide, hchar]
      simp
    rw [this, norm_zero]
  have hmain := h 2 f 0 hB 0
  have hzero : fourier f (0 : ZMod 2) = 2 := by
    rw [fourier_apply]
    rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [hf]
  rw [hzero] at hmain
  norm_num [hf] at hmain

/--
Corrected form of the requested statement: a uniform bound `B` on the nonzero Fourier
coefficients of `f` bounds the deviation of `f` from its mean `(q : ℂ)⁻¹ * fourier f 0`
by `(q - 1) * B`.
-/
theorem sub_mean_le_of_fourier_bound (f : ZMod q → ℂ) (B : ℝ)
    (hB : ∀ k : ZMod q, k ≠ 0 → ‖fourier f k‖ ≤ B) (x : ZMod q) :
    ‖f x - (q : ℂ)⁻¹ * fourier f 0‖ ≤ (q - 1 : ℕ) * B := by
  refine (sub_mean_le_of_fourier_bound_sharp f B hB x).trans ?_
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) with h1 | h2
  · simp [← h1]
  · have : Fact (1 < q) := ⟨h2⟩
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1 one_ne_zero)
    have hq1 : (q : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact mul_le_of_le_one_left (by positivity) hq1

end CharacterSums

