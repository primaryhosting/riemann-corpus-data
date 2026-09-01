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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace GoldbachSchema

/-! ## The spectral model

We build the standard finite (circle-method) spectral model for the Goldbach problem.

For a modulus `n` we let `zeta n = exp (2 π i / n)` be a primitive `n`-th root of unity and
form, for each frequency `j`, the prime exponential sum

`spectralSum n j = ∑_{p prime, p < n} (zeta n) ^ (j * p)`.

The *spectral energy* of `n` is `spectralEnergy n = ∑_{j < n} (spectralSum n j) ^ 2`.

The key intermediate result (`spectral_identity`) is the exact Fourier identity

`spectralEnergy n = n * #{(p, q) : p, q prime, p + q = n}`

for `n ≥ 4`.  Consequently, nonvanishing of the spectral energy — the *spectral model*
hypothesis — forces an actual Goldbach representation.
-/

/-- A primitive `n`-th root of unity, `exp (2 π i / n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The primes below `n`. -/
def primesBelow (n : ℕ) : Finset ℕ := (Finset.range n).filter Nat.Prime

/-- The prime exponential sum at frequency `j` and modulus `n`. -/
noncomputable def spectralSum (n j : ℕ) : ℂ := ∑ p ∈ primesBelow n, (zeta n) ^ (j * p)

/-- The spectral energy of `n`: the sum over all frequencies of the squared prime
exponential sum. -/
noncomputable def spectralEnergy (n : ℕ) : ℂ := ∑ j ∈ Finset.range n, (spectralSum n j) ^ 2

/-- The set of ordered pairs of primes below `n` summing to `n`. -/
def goldbachPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((primesBelow n) ×ˢ (primesBelow n)).filter (fun pq => pq.1 + pq.2 = n)

/-- `zeta n` is a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_zeta {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- `zeta n ^ k = 1` exactly when `n ∣ k`. -/
theorem zeta_pow_eq_one_iff {n : ℕ} (hn : n ≠ 0) (k : ℕ) : (zeta n) ^ k = 1 ↔ n ∣ k :=
  (isPrimitiveRoot_zeta hn).pow_eq_one_iff_dvd k

/-- Orthogonality of characters: summing `(zeta n ^ k) ^ j` over all frequencies `j < n`
gives `n` if `n ∣ k`, and `0` otherwise. -/
theorem sum_zeta_pow {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    ∑ j ∈ Finset.range n, ((zeta n) ^ k) ^ j = if n ∣ k then (n : ℂ) else 0 := by
  by_cases h : n ∣ k
  · simp [h, (zeta_pow_eq_one_iff hn k).2 h]
  · have hx : (zeta n) ^ k ≠ 1 := fun hc => h ((zeta_pow_eq_one_iff hn k).1 hc)
    have hxn : ((zeta n) ^ k) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, (zeta_pow_eq_one_iff hn n).2 dvd_rfl, one_pow]
    rw [geom_sum_eq hx, hxn]
    simp [h]

/-- **Key intermediate lemma (spectral identity).**
The spectral energy of `n ≥ 4` equals `n` times the number of ordered representations of
`n` as a sum of two primes. -/
theorem spectral_identity {n : ℕ} (hn : 4 ≤ n) :
    spectralEnergy n = (n : ℂ) * (goldbachPairs n).card := by
  have hn0 : n ≠ 0 := by omega
  have hstep : spectralEnergy n
      = ∑ x ∈ (primesBelow n) ×ˢ (primesBelow n), if n ∣ x.1 + x.2 then (n : ℂ) else 0 := by
    unfold spectralEnergy spectralSum
    have hsq : ∀ j : ℕ, (∑ p ∈ primesBelow n, (zeta n) ^ (j * p)) ^ 2
        = ∑ x ∈ (primesBelow n) ×ˢ (primesBelow n),
            ((zeta n) ^ (j * x.1)) * ((zeta n) ^ (j * x.2)) := by
      intro j
      rw [sq, Finset.sum_mul_sum, Finset.sum_product]
    simp only [hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [← sum_zeta_pow hn0 (x.1 + x.2)]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← pow_add, ← pow_mul]
    ring_nf
  rw [hstep]
  have hcond : ∀ x ∈ (primesBelow n) ×ˢ (primesBelow n),
      (if n ∣ x.1 + x.2 then (n : ℂ) else 0)
        = (if x.1 + x.2 = n then (n : ℂ) else 0) := by
    rintro ⟨p, q⟩ hx
    simp only [Finset.mem_product, primesBelow, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨⟨hp1, hp2⟩, hq1, hq2⟩ := hx
    have hp2' : 2 ≤ p := hp2.two_le
    have hq2' : 2 ≤ q := hq2.two_le
    have hiff : n ∣ p + q ↔ p + q = n := by
      constructor
      · rintro ⟨c, hc⟩
        have hc2 : c < 2 := by nlinarith
        interval_cases c <;> omega
      · intro he; exact he ▸ dvd_rfl
    simp only [hiff]
  rw [Finset.sum_congr rfl hcond, ← Finset.sum_filter]
  simp [goldbachPairs, mul_comm]

/-- **Goldbach from the spectral model.**

If the spectral energy `∑_{j < n} (∑_{p prime, p < n} exp (2 π i j p / n)) ^ 2` is nonzero for
every even `n ≥ 4` (the spectral model hypothesis), then every even `n ≥ 4` is a sum of two
primes.

The Fourier-analytic content — the exact identity relating the spectral energy to the Goldbach
representation count — is discharged unconditionally in `spectral_identity`; only the analytic
nonvanishing input remains as a hypothesis. -/
theorem goldbach_from_spectral_model
    (hspec : ∀ n : ℕ, 4 ≤ n → Even n → spectralEnergy n ≠ 0) :
    ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  intro n hn hev
  have hid := spectral_identity hn
  have hcard : (goldbachPairs n).card ≠ 0 := by
    intro h
    exact hspec n hn hev (by rw [hid, h]; simp)
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hcard
  simp only [goldbachPairs, Finset.mem_filter, Finset.mem_product, primesBelow,
    Finset.mem_filter, Finset.mem_range] at hx
  exact ⟨x.1, x.2, hx.1.1.2, hx.1.2.2, hx.2⟩

/-- The spectral model hypothesis is *exactly equivalent* to the Goldbach conjecture: the
spectral energy of an even `n ≥ 4` is nonzero if and only if `n` is a sum of two primes.
So the residual hypothesis of `goldbach_from_spectral_model` is not a strictly stronger
analytic assumption; it is a faithful spectral reformulation of the open problem, and all of
the Fourier-analytic content of the schema has been discharged. -/
theorem spectral_model_iff_goldbach :
    (∀ n : ℕ, 4 ≤ n → Even n → spectralEnergy n ≠ 0) ↔
      (∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) := by
  refine ⟨goldbach_from_spectral_model, ?_⟩
  intro hG n hn hev
  obtain ⟨p, q, hp, hq, hpq⟩ := hG n hn hev
  have hmem : (p, q) ∈ goldbachPairs n := by
    simp only [goldbachPairs, Finset.mem_filter, Finset.mem_product, primesBelow,
      Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨⟨by have := hq.two_le; omega, hp⟩, by have := hp.two_le; omega, hq⟩, hpq⟩
  have hpos : 0 < (goldbachPairs n).card := Finset.card_pos.mpr ⟨_, hmem⟩
  rw [spectral_identity hn]
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hc0 : ((goldbachPairs n).card : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : (goldbachPairs n).card ≠ 0)
  exact mul_ne_zero hn0 hc0

end GoldbachSchema
end Brockian

