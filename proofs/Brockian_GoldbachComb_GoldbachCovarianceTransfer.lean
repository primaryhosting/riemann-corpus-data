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

namespace Brockian.GoldbachComb

/-- The set of Goldbach parts of `n`: primes `p ≤ n` such that `n - p` is also prime.
Thus `p ∈ goldbachParts n` exactly when `p + (n - p) = n` is a Goldbach decomposition. -/
def goldbachParts (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (n - p)

@[simp] lemma mem_goldbachParts {n p : ℕ} :
    p ∈ goldbachParts n ↔ p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (n - p) := by
  simp [goldbachParts]

/-- The reflection `p ↦ n - p` maps the Goldbach parts of `n` to themselves. -/
lemma reflect_mem_goldbachParts {n p : ℕ} (hp : p ∈ goldbachParts n) :
    n - p ∈ goldbachParts n := by
  rw [mem_goldbachParts] at hp ⊢
  obtain ⟨hle, hp1, hp2⟩ := hp
  refine ⟨Nat.sub_le _ _, hp2, ?_⟩
  rwa [Nat.sub_sub_self hle]

/-- Reindexing a sum over the Goldbach parts of `n` along the reflection `p ↦ n - p`. -/
lemma sum_goldbachParts_reflect {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    ∑ p ∈ goldbachParts n, F (n - p) = ∑ p ∈ goldbachParts n, F p := by
  refine Finset.sum_nbij' (fun p => n - p) (fun p => n - p) ?_ ?_ ?_ ?_ ?_ <;>
    intro a ha
  · exact reflect_mem_goldbachParts ha
  · exact reflect_mem_goldbachParts ha
  · exact Nat.sub_sub_self (mem_goldbachParts.mp ha).1
  · exact Nat.sub_sub_self (mem_goldbachParts.mp ha).1
  · rfl

/-- The (empirical) covariance of two weights `f, g` over a finite index set `s`. -/
noncomputable def cov (s : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  (∑ p ∈ s, f p * g p) / s.card - ((∑ p ∈ s, f p) / s.card) * ((∑ p ∈ s, g p) / s.card)

/-- **Goldbach Covariance Transfer.**  For every `n` and all real weights `f, g`, the
empirical covariance of `f` and `g` over the Goldbach parts of `n` is unchanged when both
weights are transported along the Goldbach reflection `p ↦ n - p` (which exchanges the two
summands of each Goldbach decomposition of `n`). -/
theorem GoldbachCovarianceTransfer (n : ℕ) (f g : ℕ → ℝ) :
    cov (goldbachParts n) (fun p => f (n - p)) (fun p => g (n - p))
      = cov (goldbachParts n) f g := by
  unfold cov
  rw [sum_goldbachParts_reflect n f, sum_goldbachParts_reflect n g,
    sum_goldbachParts_reflect n (fun p => f p * g p)]

end Brockian.GoldbachComb

