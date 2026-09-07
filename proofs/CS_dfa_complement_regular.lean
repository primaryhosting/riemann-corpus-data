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

universe u v

namespace CS

open Language

/-- The DFA obtained from `M` by complementing its set of accepting states. -/
def dfaCompl {α : Type u} {σ : Type v} (M : DFA α σ) : DFA α σ :=
  { step := M.step, start := M.start, accept := (M.accept)ᶜ }

/-- The DFA with complemented accepting states accepts exactly the complement language. -/
theorem accepts_dfaCompl {α : Type u} {σ : Type v} (M : DFA α σ) :
    (dfaCompl M).accepts = (M.accepts)ᶜ := by
  ext x
  simp only [DFA.mem_accepts, Set.mem_compl_iff, dfaCompl]
  rfl

/-- Regular languages are closed under complement. -/
theorem dfa_complement_regular {α : Type} {L : Language α} (hL : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := hL
  exact ⟨σ, hσ, dfaCompl M, by rw [accepts_dfaCompl, hM]⟩

end CS

