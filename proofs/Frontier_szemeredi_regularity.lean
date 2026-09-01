import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
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


namespace Frontier

open Finset

/-- **Szemerédi's Regularity Lemma**. -/
theorem szemeredi_regularity (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type) (_ : DecidableEq α) (_ : Fintype α)
        (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      l ≤ Fintype.card α →
        ∃ P : Finpartition (Finset.univ : Finset α),
          P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ M ∧ P.IsUniform G ε := by
  refine ⟨SzemerediRegularity.bound ε l, ?_⟩
  intro α _ _ G _ hl
  exact _root_.szemeredi_regularity G hε hl

end Frontier

#print axioms Frontier.szemeredi_regularity

