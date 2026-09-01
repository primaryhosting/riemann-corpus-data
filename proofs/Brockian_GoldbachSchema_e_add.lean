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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.GoldbachSchema

noncomputable section

/-- The additive character `e(x) = exp(2πi x)` on the circle. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `e` turns addition into multiplication. -/
lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- `e` at an integer argument is `1`. -/
lemma e_int (m : ℤ) : e (m : ℝ) = 1 := by
  unfold e
  have h : (2 * (Real.pi : ℂ) * Complex.I * (m : ℝ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `e (k * x) = (e x) ^ k`. -/
lemma e_nat_mul (k : ℕ) (x : ℝ) : e (k * x) = (e x) ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- `e x = 1` exactly when `x` is an integer. -/
lemma e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have hx : (x : ℂ) = (j : ℂ) :=
      mul_left_cancel₀ h2
        (by linear_combination hj : (2 : ℂ) * Real.pi * Complex.I * (x : ℂ)
              = 2 * Real.pi * Complex.I * (j : ℂ))
    exact_mod_cast hx
  · rintro ⟨j, rfl⟩
    exact ⟨j, by push_cast; ring⟩

/-- Discrete orthogonality of additive characters modulo `N`. -/
lemma sum_e_orthogonality (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ k ∈ Finset.range N, e ((m * k : ℤ) / (N : ℝ)) =
      if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hterm : ∀ k ∈ Finset.range N,
      e (((m * k : ℤ) : ℝ) / (N : ℝ)) = (e ((m : ℝ) / N)) ^ k := by
    intro k _
    rw [← e_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨j, hj⟩ := hdvd
    have hx : ((m : ℤ) : ℝ) / (N : ℝ) = (j : ℝ) := by
      subst hj; push_cast; field_simp
    rw [hx, e_int, if_pos ⟨j, hj⟩]
    simp
  · have hz : e ((m : ℝ) / N) ≠ 1 := by
      intro h
      rw [e_eq_one_iff] at h
      obtain ⟨j, hj⟩ := h
      apply hdvd
      refine ⟨j, ?_⟩
      have hm : (m : ℝ) = (N : ℝ) * j := by field_simp at hj; linarith [hj]
      exact_mod_cast hm
    rw [geom_sum_eq hz]
    have hpow : (e ((m : ℝ) / N)) ^ N = 1 := by
      rw [← e_nat_mul]
      have h2 : (N : ℝ) * ((m : ℝ) / N) = ((m : ℤ) : ℝ) := by field_simp
      rw [h2, e_int]
    rw [hpow, if_neg hdvd]
    simp

/-- The exponential sum over the primes not exceeding `n`
(the "spectral" side of the circle-method model). -/
noncomputable def primeExpSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, e ((p : ℝ) * t)

/-- The set of ordered Goldbach representations of `n`. -/
noncomputable def reps (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 + pq.2 = n)

/-- The spectral (discrete circle-method) count of Goldbach representations of `n`:
the `n`-th Fourier coefficient of the square of the prime exponential sum,
sampled at the `(n+1)`-st roots of unity. -/
noncomputable def spectralCount (n : ℕ) : ℂ :=
  (1 / (n + 1 : ℂ)) *
    ∑ k ∈ Finset.range (n + 1),
      (primeExpSum n ((k : ℝ) / (n + 1))) ^ 2 * e (((-(n : ℤ) * k : ℤ) : ℝ) / (n + 1 : ℝ))

/-- The square of the prime exponential sum expands as a sum over ordered pairs of primes. -/
lemma primeExpSum_sq (n : ℕ) (t : ℝ) :
    (primeExpSum n t) ^ 2 =
      ∑ pq ∈ ((Finset.range (n + 1)).filter Nat.Prime) ×ˢ
              ((Finset.range (n + 1)).filter Nat.Prime),
        e (((pq.1 + pq.2 : ℕ) : ℝ) * t) := by
  rw [sq, primeExpSum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [← e_add]
  congr 1
  push_cast
  ring

/-- **Exactness of the spectral model**: the spectral count of `n` is precisely the
number of ordered pairs of primes summing to `n`. -/
theorem spectralCount_eq_card (n : ℕ) : spectralCount n = ((reps n).card : ℂ) := by
  set P := (Finset.range (n + 1)).filter Nat.Prime with hP
  have hNR : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hNC : ((n : ℂ) + 1) ≠ 0 := by
    have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have step1 : ∀ k ∈ Finset.range (n + 1),
      (primeExpSum n ((k : ℝ) / (n + 1))) ^ 2 * e (((-(n : ℤ) * k : ℤ) : ℝ) / (n + 1 : ℝ))
        = ∑ pq ∈ P ×ˢ P, e (((((pq.1 : ℤ) + (pq.2 : ℤ) - n) * k : ℤ) : ℝ) / (n + 1 : ℝ)) := by
    intro k _
    rw [primeExpSum_sq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun pq _ => ?_)
    rw [← e_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [spectralCount, Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ pq ∈ P ×ˢ P,
      ∑ k ∈ Finset.range (n + 1), e (((((pq.1 : ℤ) + (pq.2 : ℤ) - n) * k : ℤ) : ℝ) / (n + 1 : ℝ))
        = if pq.1 + pq.2 = n then ((n : ℂ) + 1) else 0 := by
    intro pq hpq
    have h := sum_e_orthogonality (n + 1) (Nat.succ_pos n) (((pq.1 : ℤ) + (pq.2 : ℤ) - n))
    push_cast at h ⊢
    rw [h]
    simp only [Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range] at hpq
    by_cases hs : pq.1 + pq.2 = n
    · rw [if_pos (by simp [show ((pq.1 : ℤ) + pq.2 - n) = 0 by omega]), if_pos hs]
    · rw [if_neg ?_, if_neg hs]
      intro hdvd
      have habs : ((pq.1 : ℤ) + (pq.2 : ℤ) - n) = 0 := by
        obtain ⟨c, hc⟩ := hdvd
        have h1 : ((pq.1 : ℤ) + pq.2) - n ≤ n := by omega
        have h2 : -(n : ℤ) ≤ ((pq.1 : ℤ) + pq.2) - n := by omega
        have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg _
        rcases lt_trichotomy c 0 with hc1 | hc1 | hc1
        · have hle : ((n : ℤ) + 1) * c ≤ ((n : ℤ) + 1) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by linarith)
          linarith
        · simp [hc1] at hc; linarith
        · have hle : ((n : ℤ) + 1) * 1 ≤ ((n : ℤ) + 1) * c :=
            mul_le_mul_of_nonneg_left (by omega) (by linarith)
          linarith
      omega
  rw [Finset.sum_congr rfl step2, ← Finset.sum_filter, Finset.sum_const]
  have hfilter : (P ×ˢ P).filter (fun pq => pq.1 + pq.2 = n) = reps n := by
    ext pq
    simp only [reps, hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    tauto
  rw [hfilter]
  field_simp
  ring

/-- The spectral model hypothesis: the spectral count of every even `n ≥ 4` is positive. -/
def SpectralModel : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → 0 < (spectralCount n).re

/-- Goldbach's conjecture. -/
def Goldbach : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- **Goldbach from the spectral model.**  If the spectral (circle-method) count of every
even `n ≥ 4` is positive, then every even `n ≥ 4` is a sum of two primes. -/
theorem goldbach_from_spectral_model (hspec : SpectralModel) : Goldbach := by
  intro n hev h4
  have h := hspec n hev h4
  rw [spectralCount_eq_card] at h
  simp only [Complex.natCast_re] at h
  have hcard : 0 < (reps n).card := by exact_mod_cast h
  obtain ⟨pq, hpq⟩ := Finset.card_pos.mp hcard
  simp only [reps, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq
  exact ⟨pq.1, pq.2, hpq.2.1, hpq.2.2.1, hpq.2.2.2⟩

/-- The converse: Goldbach's conjecture implies the spectral model hypothesis. -/
theorem spectralModel_of_goldbach (h : Goldbach) : SpectralModel := by
  intro n hev h4
  obtain ⟨p, q, hp, hq, hpq⟩ := h n hev h4
  rw [spectralCount_eq_card]
  simp only [Complex.natCast_re]
  have hmem : (p, q) ∈ reps n := by
    simp only [reps, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, hp, hq, hpq⟩
  have hpos : 0 < (reps n).card := Finset.card_pos.mpr ⟨_, hmem⟩
  exact_mod_cast hpos

/-- The spectral model hypothesis is *equivalent* to Goldbach's conjecture: the model is an
exact reformulation, so its hypothesis cannot be discharged without settling Goldbach itself. -/
theorem spectralModel_iff_goldbach : SpectralModel ↔ Goldbach :=
  ⟨goldbach_from_spectral_model, spectralModel_of_goldbach⟩

end

/-
Note on the "open discharge" request.

`spectralModel_iff_goldbach` shows that the spectral model hypothesis `SpectralModel` is
*logically equivalent* to Goldbach's conjecture: by `spectralCount_eq_card` the spectral count
`spectralCount n` equals, exactly, the number of ordered pairs of primes summing to `n`.
Consequently, discharging the hypothesis of `goldbach_from_spectral_model` unconditionally would
be the same thing as proving Goldbach's conjecture, which is open.  What is proved here
unconditionally and axiom-cleanly is the reduction itself, together with the exact evaluation of
the circle-method (discrete Fourier) model that underlies it.
-/

end Brockian.GoldbachSchema

