/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace PCA
namespace Isolation

/-- Guard formulas of the isolation engine's policy language: propositional
formulas over atomic capability checks indexed by natural numbers. -/
inductive Guard : Type
  | tt : Guard
  | ff : Guard
  | atom : Nat → Guard
  | neg : Guard → Guard
  | conj : Guard → Guard → Guard
  | disj : Guard → Guard → Guard
  deriving DecidableEq, Repr

namespace Guard

/-- Semantics of a guard relative to an environment assigning a truth value to
each atomic capability check. -/
def eval (env : Nat → Bool) : Guard → Bool
  | tt => true
  | ff => false
  | atom i => env i
  | neg g => !(g.eval env)
  | conj g₁ g₂ => (g₁.eval env) && (g₂.eval env)
  | disj g₁ g₂ => (g₁.eval env) || (g₂.eval env)

/-- The isolation engine's disjunction split: a guard is decomposed into the
list of its top-level disjuncts, each of which is analysed in isolation. -/
def split : Guard → List Guard
  | disj g₁ g₂ => g₁.split ++ g₂.split
  | g => [g]

@[simp] theorem split_disj (g₁ g₂ : Guard) :
    (disj g₁ g₂).split = g₁.split ++ g₂.split := rfl

/-- The split is never empty: every guard has at least one branch. -/
theorem split_ne_nil (g : Guard) : g.split ≠ [] := by
  induction g with
  | disj g₁ g₂ ih₁ _ => simpa [split] using fun h => ih₁ (List.append_eq_nil_iff.mp h).1
  | _ => simp [split]

end Guard

/-- **Disjunction split preserves semantics.**  Splitting a guard into its
top-level disjuncts, as the isolation engine does before analysing each branch
separately, is both sound and complete with respect to the guard semantics: the
guard holds in an environment exactly when one of its branches does. -/
theorem disjunction_split_preserves_semantics (env : Nat → Bool) (g : Guard) :
    g.eval env = true ↔ ∃ b ∈ g.split, b.eval env = true := by
  induction g with
  | disj g₁ g₂ ih₁ ih₂ =>
      simp only [Guard.eval, Guard.split_disj, List.mem_append, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · obtain ⟨b, hb, hb'⟩ := ih₁.mp h
          exact ⟨b, Or.inl hb, hb'⟩
        · obtain ⟨b, hb, hb'⟩ := ih₂.mp h
          exact ⟨b, Or.inr hb, hb'⟩
      · rintro ⟨b, hb | hb, hb'⟩
        · exact Or.inl (ih₁.mpr ⟨b, hb, hb'⟩)
        · exact Or.inr (ih₂.mpr ⟨b, hb, hb'⟩)
  | _ => simp [Guard.split]

/-- Soundness direction: if some branch of the split holds, the original guard
holds. -/
theorem split_sound (env : Nat → Bool) (g : Guard) (b : Guard)
    (hb : b ∈ g.split) (h : b.eval env = true) : g.eval env = true :=
  (disjunction_split_preserves_semantics env g).mpr ⟨b, hb, h⟩

/-- Completeness direction: if the guard holds, some branch of the split
holds. -/
theorem split_complete (env : Nat → Bool) (g : Guard) (h : g.eval env = true) :
    ∃ b ∈ g.split, b.eval env = true :=
  (disjunction_split_preserves_semantics env g).mp h

end Isolation
end PCA

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

