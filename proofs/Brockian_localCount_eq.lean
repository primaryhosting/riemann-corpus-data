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

/-- The **local count** of a constellation with shift set `H` at modulus `n`:
the number of residues `a : ZMod n` such that none of the shifted values `a + h`
(`h ∈ H`) vanishes modulo `n`.  This is the local factor appearing in the
singular series of a constellation / prime-tuple counting problem. -/
noncomputable def localCount (n : ℕ) [NeZero n] (H : Finset (ZMod n)) : ℕ :=
  (Finset.univ.filter (fun a : ZMod n => ∀ h ∈ H, a + h ≠ 0)).card

/-- The local count of a shift set `H` modulo `n` is `n - |H|`: the forbidden
residues are exactly the negatives `-h` of the elements of `H`, and negation is
injective (`neg_injective`), so the excluded set has exactly `|H|` elements
(`Finset.card_image_of_injective`, `Finset.card_univ_diff`, `ZMod.card`). -/
theorem localCount_eq (n : ℕ) [NeZero n] (H : Finset (ZMod n)) :
    localCount n H = n - H.card := by
  have hset : (Finset.univ.filter (fun a : ZMod n => ∀ h ∈ H, a + h ≠ 0))
      = Finset.univ \ H.image (fun h => -h) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_image, not_exists, not_and]
    constructor
    · intro h x hx hxa
      exact h x hx (by rw [← hxa]; exact neg_add_cancel x)
    · intro h x hx hxa
      exact h x hx (neg_eq_of_add_eq_zero_left hxa)
  have himg : (H.image (fun h => -h)).card = H.card :=
    Finset.card_image_of_injective _ neg_injective
  rw [localCount, hset, Finset.card_univ_diff, himg, ZMod.card]

/-- Local count of a one-element (`k = 1`) constellation. -/
theorem ConstellationLocalCountK1 (n : ℕ) [NeZero n] (h₁ : ZMod n) :
    localCount n {h₁} = n - 1 := by
  rw [localCount_eq, Finset.card_singleton]

/-- Local count of a two-element (`k = 2`) constellation with distinct shifts. -/
theorem ConstellationLocalCountK2 (n : ℕ) [NeZero n] (h₁ h₂ : ZMod n)
    (h12 : h₁ ≠ h₂) :
    localCount n {h₁, h₂} = n - 2 := by
  rw [localCount_eq]
  congr 1
  rw [Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]

/-- **Main result.** Local count of a three-element (`k = 3`) constellation:
if the shifts `h₁, h₂, h₃` are pairwise distinct modulo `n`, then exactly
`n - 3` residues `a` avoid all three forbidden classes. -/
theorem ConstellationLocalCountK3 (n : ℕ) [NeZero n] (h₁ h₂ h₃ : ZMod n)
    (h12 : h₁ ≠ h₂) (h13 : h₁ ≠ h₃) (h23 : h₂ ≠ h₃) :
    localCount n {h₁, h₂, h₃} = n - 3 := by
  rw [localCount_eq]
  congr 1
  rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
    Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]

/-- Product form of the `k = 3` local count over a prime modulus: since `ZMod p`
is an integral domain, the admissible residues are exactly those for which the
product `(a + h₁)(a + h₂)(a + h₃)` is nonzero, and there are `p - 3` of them. -/
theorem ConstellationLocalCountK3_prod (p : ℕ) [Fact (Nat.Prime p)]
    (h₁ h₂ h₃ : ZMod p) (h12 : h₁ ≠ h₂) (h13 : h₁ ≠ h₃) (h23 : h₂ ≠ h₃) :
    (Finset.univ.filter
        (fun a : ZMod p => (a + h₁) * (a + h₂) * (a + h₃) ≠ 0)).card = p - 3 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  rw [← ConstellationLocalCountK3 p h₁ h₂ h₃ h12 h13 h23]
  unfold localCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, mul_eq_zero,
    not_or, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  tauto

end Brockian

