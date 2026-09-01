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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.GoldbachComb

/-- The primes not exceeding `N`. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- All ordered pairs of primes not exceeding `N`. -/
def goldbachPairs (N : ℕ) : Finset (ℕ × ℕ) := primesUpTo N ×ˢ primesUpTo N

/-- The Goldbach representation count of `n` restricted to primes `≤ N`:
the number of *ordered* pairs `(p, q)` of primes `≤ N` with `p + q = n`. -/
def goldbachCount (N n : ℕ) : ℕ :=
  ((goldbachPairs N).filter fun pq => pq.1 + pq.2 = n).card

/-- The (unnormalised) weighted covariance of `f` and `g` over the finite index set `s`
with weights `w`:  `(∑ w) * (∑ w f g) - (∑ w f) * (∑ w g)`.
This is `(∑ w)^2` times the usual covariance with respect to the probability measure
obtained by normalising `w`, and is well defined even when the total weight vanishes. -/
noncomputable def wCov {ι : Type*} (s : Finset ι) (w f g : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (f i * g i))
    - (∑ i ∈ s, w i * f i) * (∑ i ∈ s, w i * g i)

lemma mem_primesUpTo {N p : ℕ} : p ∈ primesUpTo N ↔ p ≤ N ∧ p.Prime := by
  simp [primesUpTo]

lemma mem_goldbachPairs {N : ℕ} {pq : ℕ × ℕ} :
    pq ∈ goldbachPairs N ↔ (pq.1 ≤ N ∧ pq.1.Prime) ∧ (pq.2 ≤ N ∧ pq.2.Prime) := by
  simp [goldbachPairs, mem_primesUpTo]

/-- The Goldbach count is positive exactly when `n` is a sum of two primes `≤ N`. -/
lemma goldbachCount_pos_iff (N n : ℕ) :
    0 < goldbachCount N n ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ N ∧ q ≤ N ∧ p + q = n := by
  rw [goldbachCount, Finset.card_pos]
  constructor
  · rintro ⟨pq, hpq⟩
    rw [Finset.mem_filter, mem_goldbachPairs] at hpq
    exact ⟨pq.1, pq.2, hpq.1.1.2, hpq.1.2.2, hpq.1.1.1, hpq.1.2.1, hpq.2⟩
  · rintro ⟨p, q, hp, hq, hpN, hqN, hsum⟩
    exact ⟨(p, q), by
      rw [Finset.mem_filter, mem_goldbachPairs]
      exact ⟨⟨⟨hpN, hp⟩, hqN, hq⟩, hsum⟩⟩

/-- Every Goldbach pair from primes `≤ N` sums into `Finset.range (2 * N + 1)`. -/
lemma sum_mem_range {N : ℕ} {pq : ℕ × ℕ} (h : pq ∈ goldbachPairs N) :
    pq.1 + pq.2 ∈ Finset.range (2 * N + 1) := by
  rw [mem_goldbachPairs] at h
  simp only [Finset.mem_range]
  omega

/-- **Sum transfer**: a sum of `h (p + q)` over ordered pairs of primes `≤ N`
equals the sum of `h n` weighted by the Goldbach representation count of `n`. -/
theorem goldbach_sum_transfer (N : ℕ) (h : ℕ → ℝ) :
    ∑ pq ∈ goldbachPairs N, h (pq.1 + pq.2)
      = ∑ n ∈ Finset.range (2 * N + 1), (goldbachCount N n : ℝ) * h n := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun pq : ℕ × ℕ => pq.1 + pq.2)
        (fun _ hx => sum_mem_range hx) (f := fun pq : ℕ × ℕ => h (pq.1 + pq.2))]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [Finset.sum_congr rfl (g := fun _ => h n) ?_, Finset.sum_const, goldbachCount,
    nsmul_eq_mul]
  intro pq hpq
  rw [(Finset.mem_filter.mp hpq).2]

/-- The total Goldbach weight is the square of the number of primes `≤ N`. -/
theorem sum_goldbachCount (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N + 1), goldbachCount N n = (primesUpTo N).card ^ 2 := by
  have := Finset.card_eq_sum_card_fiberwise
    (f := fun pq : ℕ × ℕ => pq.1 + pq.2) (s := goldbachPairs N)
    (t := Finset.range (2 * N + 1)) (fun _ hx => sum_mem_range hx)
  simp only [goldbachPairs, Finset.card_product] at this
  simp only [goldbachCount, goldbachPairs, sq]
  exact this.symm

/-- **Goldbach Covariance Transfer.**

The (unnormalised) covariance of the two observables `f ∘ σ` and `g ∘ σ`, where
`σ (p, q) = p + q`, computed over the uniformly weighted set of ordered pairs of
primes `≤ N`, coincides with the covariance of `f` and `g` computed over the integers
`n ≤ 2 * N` weighted by the Goldbach representation count `goldbachCount N n`.

In other words, the pair statistics of the Goldbach convolution transfer exactly to the
counting-function statistics: nothing is lost by pushing the uniform measure on prime
pairs forward along the addition map. -/
theorem GoldbachCovarianceTransfer (N : ℕ) (f g : ℕ → ℝ) :
    wCov (goldbachPairs N) (fun _ => 1)
        (fun pq => f (pq.1 + pq.2)) (fun pq => g (pq.1 + pq.2))
      = wCov (Finset.range (2 * N + 1)) (fun n => (goldbachCount N n : ℝ)) f g := by
  unfold wCov
  have h1 := goldbach_sum_transfer N (fun _ => 1)
  have hfg := goldbach_sum_transfer N (fun n => f n * g n)
  have hf := goldbach_sum_transfer N f
  have hg := goldbach_sum_transfer N g
  simp only [one_mul, mul_one] at *
  rw [h1, hfg, hf, hg]

end Brockian.GoldbachComb

#print axioms Brockian.GoldbachComb.GoldbachCovarianceTransfer

