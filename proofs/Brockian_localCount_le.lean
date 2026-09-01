/- (Lean requires `import` lines to precede any module docstring, so the mandated
header is reproduced verbatim inside this plain comment.)
/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators

namespace Brockian

/-- The local count of a `k`-tuple `H` of integers at a modulus `p`: the number of
distinct residue classes modulo `p` occupied by the entries of `H`. -/
noncomputable def localCount {k : ℕ} (p : ℕ) (H : Fin k → ℤ) : ℕ :=
  (Finset.univ.image fun i => ((H i : ZMod p))).card

/-- A tuple is admissible when, for every prime `p`, it misses at least one residue class
modulo `p`. -/
def Admissible {k : ℕ} (H : Fin k → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → localCount p H < p

/-- The local count of a `k`-tuple never exceeds `k`. -/
theorem localCount_le {k : ℕ} (p : ℕ) (H : Fin k → ℤ) : localCount p H ≤ k := by
  refine le_trans (Finset.card_image_le) ?_
  simp

theorem localCount_two_zero_two_six : localCount 2 ![0, 2, 6] = 1 := by
  decide

theorem localCount_three_zero_two_six : localCount 3 ![0, 2, 6] = 2 := by
  decide

/-- **Constellation local count, k = 3.**  For every prime `p`:
the local count of any triple of integers is at most `3`, and the triple `(0, 2, 6)`
is locally admissible at `p`, i.e. it omits at least one residue class mod `p`.
Consequently `(0,2,6)` is an admissible constellation. -/
theorem ConstellationLocalCountK3 :
    (∀ (p : ℕ) (H : Fin 3 → ℤ), localCount p H ≤ 3) ∧ Admissible ![0, 2, 6] := by
  refine ⟨fun p H => localCount_le p H, ?_⟩
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [localCount_two_zero_two_six]; norm_num
  rcases eq_or_ne p 3 with rfl | hp3
  · rw [localCount_three_zero_two_six]; norm_num
  have h5 : 5 ≤ p := by
    by_contra hlt
    push_neg at hlt
    have h2 := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  exact lt_of_le_of_lt (localCount_le p ![0, 2, 6]) (by omega)

end Brockian

#print axioms Brockian.ConstellationLocalCountK3

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

