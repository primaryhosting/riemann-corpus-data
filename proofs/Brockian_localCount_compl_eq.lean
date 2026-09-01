/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

namespace Brockian

/-- The local count of a constellation (`k`-tuple of shifts) `H` modulo `p`:
the number of residues `n` mod `p` such that none of the shifted values
`n + H i` is divisible by `p`. -/
noncomputable def localCount {p : ℕ} [NeZero p] {k : ℕ} (H : Fin k → ZMod p) : ℕ :=
  (Finset.univ.filter fun n : ZMod p => ∀ i : Fin k, n + H i ≠ 0).card

/-- The excluded residues are exactly the negatives of the shifts. -/
theorem localCount_compl_eq {p : ℕ} [NeZero p] {k : ℕ} (H : Fin k → ZMod p) :
    (Finset.univ.filter fun n : ZMod p => ∀ i : Fin k, n + H i ≠ 0)
      = Finset.univ \ (Finset.univ.image fun i : Fin k => -H i) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image, not_exists]
  constructor
  · intro h i hi
    exact h i (by linear_combination -hi)
  · intro h i hi
    exact h i (by linear_combination -hi)

/-- General local count: for an injective tuple of shifts, exactly `k` residues are
excluded, so the local count is `p - k`. -/
theorem localCount_of_injective {p : ℕ} [NeZero p] {k : ℕ} (H : Fin k → ZMod p)
    (hH : Function.Injective H) : localCount H = p - k := by
  have hinj : Function.Injective fun i : Fin k => -H i := fun i j hij => hH (by
    simpa using neg_injective hij)
  have hcard : (Finset.univ.image fun i : Fin k => -H i).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [localCount, localCount_compl_eq, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, hcard,
    ZMod.card]

/-- **Constellation local count, `k = 3`.**  For a modulus `p` and three shifts
`h₀, h₁, h₂` that are pairwise distinct modulo `p`, the number of residues `n` mod `p`
avoiding all three shifted zeros is `p - 3`. -/
theorem ConstellationLocalCountK3 {p : ℕ} [NeZero p] (h₀ h₁ h₂ : ZMod p)
    (h01 : h₀ ≠ h₁) (h02 : h₀ ≠ h₂) (h12 : h₁ ≠ h₂) :
    (Finset.univ.filter fun n : ZMod p => n + h₀ ≠ 0 ∧ n + h₁ ≠ 0 ∧ n + h₂ ≠ 0).card
      = p - 3 := by
  have hfun : Function.Injective (![h₀, h₁, h₂]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := localCount_of_injective (![h₀, h₁, h₂]) hfun
  rw [localCount] at h
  rw [← h]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, b, c⟩ i
    fin_cases i <;> simpa
  · intro hn
    exact ⟨by simpa using hn 0, by simpa using hn 1, by simpa using hn 2⟩

end Brockian

