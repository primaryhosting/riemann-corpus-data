/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The local count of a constellation (admissible tuple) `H` at the prime `p`:
the number of residue classes `n` mod `p` such that `n + h ≢ 0 (mod p)` for every
shift `h ∈ H`, i.e. the number of residues that survive the sieve at `p`. -/
noncomputable def localConstellationCount (p : ℕ) [NeZero p] (H : Finset (ZMod p)) : ℕ :=
  (Finset.univ.filter fun n : ZMod p => ∀ h ∈ H, n + h ≠ 0).card

/-- The set of residues killed at `p` by the three shifts `h₁, h₂, h₃` is exactly
`{-h₁, -h₂, -h₃}`. -/
theorem killed_set_k3 (p : ℕ) [hp : Fact p.Prime] (h₁ h₂ h₃ : ZMod p) :
    (Finset.univ.filter fun n : ZMod p => (n + h₁) * (n + h₂) * (n + h₃) = 0)
      = ({-h₁, -h₂, -h₃} : Finset (ZMod p)) := by
  ext n
  simp [mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

/-- Three pairwise distinct shifts kill exactly three residue classes. -/
theorem card_killed_set_k3 (p : ℕ) (h₁ h₂ h₃ : ZMod p)
    (h12 : h₁ ≠ h₂) (h13 : h₁ ≠ h₃) (h23 : h₂ ≠ h₃) :
    ({-h₁, -h₂, -h₃} : Finset (ZMod p)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23])]
  simp

/--
**Constellation local count for `k = 3`.**

For a prime `p` and a triple of shifts `h₁, h₂, h₃` in `ZMod p`:

* the local count of the constellation `{h₁, h₂, h₃}` equals the number of residues `n`
  with `(n + h₁)(n + h₂)(n + h₃) ≠ 0` (the product form of the sieve condition);
* it equals `p` minus the number of distinct residues killed, namely `#{-h₁, -h₂, -h₃}`;
* in particular, if the three shifts are pairwise distinct mod `p`, the count is `p - 3`.
-/
theorem ConstellationLocalCountK3 (p : ℕ) [hp : Fact p.Prime] (h₁ h₂ h₃ : ZMod p) :
    localConstellationCount p {h₁, h₂, h₃}
        = (Finset.univ.filter fun n : ZMod p => (n + h₁) * (n + h₂) * (n + h₃) ≠ 0).card
      ∧ localConstellationCount p {h₁, h₂, h₃}
        = p - ({-h₁, -h₂, -h₃} : Finset (ZMod p)).card
      ∧ (h₁ ≠ h₂ → h₁ ≠ h₃ → h₂ ≠ h₃ →
          localConstellationCount p {h₁, h₂, h₃} = p - 3) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- The sieve condition for the triple is the non-vanishing of the product.
  have hprod : localConstellationCount p {h₁, h₂, h₃}
      = (Finset.univ.filter fun n : ZMod p => ¬ ((n + h₁) * (n + h₂) * (n + h₃) = 0)).card := by
    unfold localConstellationCount
    refine congrArg Finset.card ?_
    ext n
    simp [Finset.mem_insert, mul_eq_zero, not_or, forall_eq_or_imp, and_assoc]
  -- Counting: survivors = p - killed.
  have hcard : Finset.card (Finset.univ : Finset (ZMod p)) = p := by simp [ZMod.card]
  have key := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod p)))
      (p := fun n => (n + h₁) * (n + h₂) * (n + h₃) = 0)
  rw [killed_set_k3 p h₁ h₂ h₃, hcard] at key
  refine ⟨hprod, by omega, fun h12 h13 h23 => ?_⟩
  rw [card_killed_set_k3 p h₁ h₂ h₃ h12 h13 h23] at key
  omega

end Brockian

