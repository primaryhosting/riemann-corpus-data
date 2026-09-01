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

import Mathlib

/-!
# A spectral (circle-method) schema for the Goldbach conjecture

This file sets up the "spectral model" for the binary Goldbach problem: the number of
representations of `n` as an ordered sum of two primes is computed by an exponential-sum
(Fourier) integral over the unit circle, and Goldbach's conjecture is exactly the
statement that this integral is positive for every even `n ≥ 4`.

Main results:

* `Brockian.GoldbachSchema.spectral_identity` : the Fourier integral of the squared prime
  exponential sum equals the representation count. This is the unconditional analytic input.
* `Brockian.GoldbachSchema.goldbach_from_spectral_model` : from the spectral positivity
  hypothesis one deduces Goldbach's conjecture.
* `Brockian.GoldbachSchema.spectralPositivity_iff_goldbach` : the spectral positivity
  hypothesis is *equivalent* to Goldbach's conjecture, so it cannot be discharged without
  proving Goldbach itself.
* `Brockian.GoldbachSchema.goldbach_below_two_hundred` : an unconditional finite verification.
-/

namespace Brockian.GoldbachSchema

open Complex Real Finset

/-- The primes not exceeding `n`. -/
def primesUpTo (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

/-- Ordered pairs of primes summing to `n`. -/
def goldbachPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (primesUpTo n ×ˢ primesUpTo n).filter (fun pq => pq.1 + pq.2 = n)

/-- The number of ordered representations of `n` as a sum of two primes. -/
def repCount (n : ℕ) : ℕ := (goldbachPairs n).card

/-- `n` is a sum of two primes. -/
def GoldbachAt (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Goldbach's conjecture. -/
def Goldbach : Prop := ∀ n : ℕ, 4 ≤ n → Even n → GoldbachAt n

/-- The additive character `a ↦ e(k a)`. -/
noncomputable def chr (k : ℤ) (a : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * a)

/-- The prime exponential sum `S_n(a) = ∑_{p ≤ n} e(p a)`. -/
noncomputable def primeExpSum (n : ℕ) (a : ℝ) : ℂ :=
  ∑ p ∈ primesUpTo n, chr (p : ℤ) a

/-- The circle-method integral `∫_0^1 S_n(a)^2 e(-n a) da`. -/
noncomputable def spectralIntegral (n : ℕ) : ℂ :=
  ∫ a in (0:ℝ)..1, (primeExpSum n a) ^ 2 * chr (-(n : ℤ)) a

/-- The spectral model hypothesis: the circle-method integral is positive for every even
`n ≥ 4`. -/
def SpectralPositivity : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → 0 < (spectralIntegral n).re

/-! ### Orthogonality -/

theorem integral_chr (k : ℤ) : (∫ a in (0:ℝ)..1, chr k a) = if k = 0 then 1 else 0 := by
  unfold chr
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * k) ≠ 0 := by
      simp [Real.pi_ne_zero, hk, Complex.ext_iff]
    have h2 := integral_exp_mul_complex (a := (0:ℝ)) (b := (1:ℝ)) hc
    simp only [mul_assoc] at h2 ⊢
    rw [h2]
    have h3 : Complex.exp (2 * ((Real.pi : ℂ) * (Complex.I * ((k : ℂ) * ((1:ℝ) : ℂ))))) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]; ring_nf; norm_num
    rw [h3]
    simp

theorem continuous_chr (k : ℤ) : Continuous (chr k) := by
  unfold chr
  exact Complex.continuous_exp.comp (by fun_prop)

theorem chr_mul (j k : ℤ) (a : ℝ) : chr j a * chr k a = chr (j + k) a := by
  unfold chr
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-! ### The spectral identity -/

theorem integrand_eq (n : ℕ) (a : ℝ) :
    (primeExpSum n a) ^ 2 * chr (-(n : ℤ)) a =
      ∑ x ∈ primesUpTo n ×ˢ primesUpTo n, chr ((x.1 : ℤ) + (x.2 : ℤ) - (n : ℤ)) a := by
  rw [Finset.sum_product' (s := primesUpTo n) (t := primesUpTo n)
    (f := fun i j => chr ((i : ℤ) + (j : ℤ) - (n : ℤ)) a)]
  unfold primeExpSum
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [chr_mul, chr_mul]
  ring_nf

theorem spectral_identity (n : ℕ) : spectralIntegral n = (repCount n : ℂ) := by
  unfold spectralIntegral
  rw [intervalIntegral.integral_congr (g := fun a =>
        ∑ x ∈ primesUpTo n ×ˢ primesUpTo n, chr ((x.1 : ℤ) + (x.2 : ℤ) - (n : ℤ)) a)
      (fun a _ => integrand_eq n a)]
  rw [intervalIntegral.integral_finset_sum
    (fun x _ => ((continuous_chr ((x.1 : ℤ) + (x.2 : ℤ) - (n : ℤ))).intervalIntegrable _ _))]
  have hterm : ∀ x ∈ primesUpTo n ×ˢ primesUpTo n,
      (∫ a in (0:ℝ)..1, chr ((x.1 : ℤ) + (x.2 : ℤ) - (n : ℤ)) a) =
        if x.1 + x.2 = n then (1 : ℂ) else 0 := by
    intro x _
    rw [integral_chr]
    by_cases h : x.1 + x.2 = n
    · rw [if_pos (by omega : (x.1 : ℤ) + (x.2 : ℤ) - (n : ℤ) = 0), if_pos h]
    · rw [if_neg, if_neg h]
      omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  rfl

/-! ### The conditional theorem and its converse -/

theorem goldbachAt_iff_repCount_pos (n : ℕ) : GoldbachAt n ↔ 0 < repCount n := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    refine Finset.card_pos.mpr ⟨(p, q), ?_⟩
    simp only [goldbachPairs, Finset.mem_filter, Finset.mem_product, primesUpTo,
      Finset.mem_range]
    exact ⟨⟨⟨by omega, hp⟩, ⟨by omega, hq⟩⟩, hpq⟩
  · intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h
    simp only [goldbachPairs, Finset.mem_filter, Finset.mem_product, primesUpTo,
      Finset.mem_range] at hx
    exact ⟨x.1, x.2, hx.1.1.2, hx.1.2.2, hx.2⟩

/-- **Goldbach from the spectral model.** If the circle-method integral attached to every
even `n ≥ 4` has positive real part, then every even `n ≥ 4` is a sum of two primes. -/
theorem goldbach_from_spectral_model (hspec : SpectralPositivity) : Goldbach := by
  intro n hn hev
  have h := hspec n hn hev
  rw [spectral_identity] at h
  simp only [Complex.natCast_re] at h
  exact (goldbachAt_iff_repCount_pos n).mpr (by exact_mod_cast h)

/-- The spectral positivity hypothesis is *equivalent* to Goldbach's conjecture. -/
theorem spectralPositivity_iff_goldbach : SpectralPositivity ↔ Goldbach := by
  refine ⟨goldbach_from_spectral_model, fun hG n hn hev => ?_⟩
  rw [spectral_identity]
  simpa using (goldbachAt_iff_repCount_pos n).mp (hG n hn hev)

/-! ### Unconditional finite verification -/

set_option maxRecDepth 100000 in
theorem repCount_pos_of_mem_Icc (m : ℕ) (hm : m ∈ Finset.Icc 2 100) :
    0 < repCount (m + m) := by
  revert m
  decide

/-- Unconditional verification of Goldbach's conjecture for all even `n` with `4 ≤ n ≤ 200`. -/
theorem goldbach_below_two_hundred (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 200) (hev : Even n) :
    GoldbachAt n := by
  rw [goldbachAt_iff_repCount_pos]
  obtain ⟨m, rfl⟩ := hev
  exact repCount_pos_of_mem_Icc m (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

/-!
### Status of the named hypothesis

`goldbach_from_spectral_model` is a conditional theorem whose hypothesis is
`SpectralPositivity`. By `spectralPositivity_iff_goldbach` that hypothesis is logically
*equivalent* to Goldbach's conjecture itself, so it cannot be discharged by any argument
short of a proof of Goldbach; the conjecture is open. What is discharged unconditionally
here is the analytic content of the spectral model, namely the exact Fourier identity
`spectral_identity`, together with the finite verification `goldbach_below_two_hundred`.
-/

end Brockian.GoldbachSchema

