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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The *local count* of a shift pattern `H` at modulus `n`: the number of residues
`a : ZMod n` for which none of the shifted values `a + h`, `h ∈ H`, vanishes modulo `n`.
For a prime `n = p` this is the quantity `ν_H(p)` occurring in the singular series of the
Hardy–Littlewood prime constellation conjecture. -/
def localCount (H : Finset ℤ) (n : ℕ) [NeZero n] : ℕ :=
  ((Finset.univ : Finset (ZMod n)).filter fun a => ∀ h ∈ H, a + (h : ZMod n) ≠ 0).card

/-- The admissible residues are exactly the complement of the set of forbidden residues
`{-h : h ∈ H}`. -/
theorem localCount_filter_eq_compl (H : Finset ℤ) (n : ℕ) [NeZero n] :
    ((Finset.univ : Finset (ZMod n)).filter fun a => ∀ h ∈ H, a + (h : ZMod n) ≠ 0)
      = (Finset.univ : Finset (ZMod n)) \ Finset.image (fun h : ℤ => -(h : ZMod n)) H := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image, not_exists, not_and]
  constructor
  · intro ha h hh hcon
    exact ha h hh (by rw [← hcon]; ring)
  · intro ha h hh hcon
    exact ha h hh (by linear_combination -hcon)

/-- General formula: the local count is the modulus minus the number of distinct forbidden
residues `-h`, `h ∈ H`. -/
theorem localCount_eq (H : Finset ℤ) (n : ℕ) [NeZero n] :
    localCount H n = n - (Finset.image (fun h : ℤ => -(h : ZMod n)) H).card := by
  rw [localCount, localCount_filter_eq_compl,
    Finset.card_univ_diff, ZMod.card]

/-- **Local constellation count for `k = 3`.**
For a triple of shifts `h₁, h₂, h₃` and any modulus `n ≥ 1`, the number of residues
`a : ZMod n` such that `a + h₁`, `a + h₂` and `a + h₃` are all nonzero mod `n` equals
`n` minus the number of distinct residues among `-h₁, -h₂, -h₃`; in particular it lies
between `n - 3` and `n`. -/
theorem ConstellationLocalCountK3 (n : ℕ) [NeZero n] (h₁ h₂ h₃ : ℤ) :
    localCount {h₁, h₂, h₃} n
        = n - ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card ∧
      n - 3 ≤ localCount {h₁, h₂, h₃} n ∧ localCount {h₁, h₂, h₃} n ≤ n := by
  have himg : Finset.image (fun h : ℤ => -(h : ZMod n)) {h₁, h₂, h₃}
      = ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, (rfl | rfl | rfl), rfl⟩ <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨h₁, by simp⟩, ⟨h₂, by simp⟩, ⟨h₃, by simp⟩]
  have hcount : localCount {h₁, h₂, h₃} n
      = n - ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card := by
    rw [localCount_eq, himg]
  have hcard : ({-(h₁ : ZMod n), -(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h2 : ({-(h₂ : ZMod n), -(h₃ : ZMod n)} : Finset (ZMod n)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  exact ⟨hcount, by omega, by omega⟩

/-- The prime case: for `p` prime and three shifts that are pairwise distinct modulo `p`,
the local factor of the `3`-tuple constellation equals `p - 3`. -/
theorem constellationLocalCountK3_prime (p : ℕ) (hp : p.Prime) (h₁ h₂ h₃ : ℤ)
    (h12 : (h₁ : ZMod p) ≠ (h₂ : ZMod p)) (h13 : (h₁ : ZMod p) ≠ (h₃ : ZMod p))
    (h23 : (h₂ : ZMod p) ≠ (h₃ : ZMod p)) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    localCount {h₁, h₂, h₃} p = p - 3 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := (ConstellationLocalCountK3 p h₁ h₂ h₃).1
  have hne12 : -(h₁ : ZMod p) ≠ -(h₂ : ZMod p) := fun hc => h12 (neg_injective hc)
  have hne13 : -(h₁ : ZMod p) ≠ -(h₃ : ZMod p) := fun hc => h13 (neg_injective hc)
  have hne23 : -(h₂ : ZMod p) ≠ -(h₃ : ZMod p) := fun hc => h23 (neg_injective hc)
  rw [h, Finset.card_insert_of_notMem (by simp [hne12, hne13]),
    Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]

end Brockian

