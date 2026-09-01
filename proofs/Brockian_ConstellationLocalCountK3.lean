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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The local count, modulo `p`, of a constellation with offset set `A`:
the number of residues `n : ZMod p` such that none of the shifted values `n + a`
(for `a ∈ A`) is divisible by `p`. -/
def localCount (p : ℕ) [NeZero p] (A : Finset (ZMod p)) : ℕ :=
  (Finset.univ.filter (fun n : ZMod p => ∀ a ∈ A, n + a ≠ 0)).card

/-- The set of admissible residues is exactly the complement of `-A`. -/
theorem localCount_filter_eq (p : ℕ) [NeZero p] (A : Finset (ZMod p)) :
    (Finset.univ.filter (fun n : ZMod p => ∀ a ∈ A, n + a ≠ 0))
      = (A.image (fun a => -a))ᶜ := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
    Finset.mem_image, not_exists, not_and]
  constructor
  · intro h a ha hna
    exact h a ha (by rw [← hna]; ring)
  · intro h a ha hna
    exact h a ha (by linear_combination -hna)

/-- General local count formula: the number of admissible residues is `p - |A|`. -/
theorem localCount_eq (p : ℕ) [NeZero p] (A : Finset (ZMod p)) :
    localCount p A = p - A.card := by
  have hinj : Function.Injective (fun a : ZMod p => -a) := neg_injective
  rw [localCount, localCount_filter_eq, Finset.card_compl,
    Finset.card_image_of_injective _ hinj, ZMod.card]

/-- **Constellation local count, `k = 3`.**  For a constellation given by three offsets
`a b c : ZMod p` that are pairwise distinct modulo `p`, the number of residues `n mod p`
avoiding all three forbidden classes is exactly `p - 3`. -/
theorem ConstellationLocalCountK3 (p : ℕ) [NeZero p] (a b c : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    localCount p {a, b, c} = p - 3 := by
  rw [localCount_eq]
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

/-- Sanity check: modulo `7`, the constellation with offsets `{1, 2, 3}` has `7 - 3 = 4`
admissible residues. -/
example : localCount 7 {1, 2, 3} = 4 := by decide

end Brockian

