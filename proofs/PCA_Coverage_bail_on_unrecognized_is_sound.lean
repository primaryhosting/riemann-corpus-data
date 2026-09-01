/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Coverage

/-- A model of an isolation engine.

* `recognized i` says the engine's coverage analysis recognizes the input `i`
  (i.e. the input falls inside the modelled fragment).
* `step s i` is the effect of handling input `i` in state `s`.
* `Safe s` is the safety invariant the engine is supposed to maintain.
* `step_safe` is the *coverage obligation*: the engine is only verified to
  preserve safety on recognized inputs. Nothing at all is assumed about the
  behaviour of `step` on unrecognized inputs.
-/
structure Engine (Input State : Type u) where
  recognized : Input → Bool
  step : State → Input → State
  Safe : State → Prop
  step_safe : ∀ s i, Safe s → recognized i = true → Safe (step s i)

variable {Input State : Type u}

/-- Running a trace of inputs through the engine, *bailing out* (returning `none`)
as soon as an unrecognized input is encountered. -/
def Engine.runTrace (E : Engine Input State) : State → List Input → Option State
  | s, [] => some s
  | s, i :: rest => if E.recognized i then E.runTrace (E.step s i) rest else none

@[simp] theorem Engine.runTrace_nil (E : Engine Input State) (s : State) :
    E.runTrace s [] = some s := rfl

@[simp] theorem Engine.runTrace_cons (E : Engine Input State) (s : State)
    (i : Input) (rest : List Input) :
    E.runTrace s (i :: rest) =
      if E.recognized i then E.runTrace (E.step s i) rest else none := rfl

/-- **Soundness of bailing out on unrecognized inputs.**

For any engine whose `step` is only known to preserve the safety invariant on
*recognized* inputs, the bail-on-unrecognized driver is sound and complete:

* (soundness) every state it actually produces satisfies the invariant, and
* (completeness of the bail) it bails out exactly when the trace contains an
  input outside the recognized fragment.

In particular no unrecognized input is ever handled, so the unverified
behaviour of `step` outside the modelled fragment can never break safety. -/
theorem bail_on_unrecognized_is_sound (E : Engine Input State)
    (tr : List Input) (s : State) (hs : E.Safe s) :
    (∀ s', E.runTrace s tr = some s' → E.Safe s') ∧
      (E.runTrace s tr = none ↔ ∃ i ∈ tr, E.recognized i = false) := by
  induction tr generalizing s with
  | nil => simp [hs]
  | cons i rest ih =>
    by_cases h : E.recognized i = true
    · have hstep := ih (E.step s i) (E.step_safe s i hs h)
      refine ⟨?_, ?_⟩
      · intro s' hs'
        rw [Engine.runTrace_cons, if_pos h] at hs'
        exact hstep.1 s' hs'
      · rw [Engine.runTrace_cons, if_pos h, hstep.2]
        constructor
        · rintro ⟨j, hj, hj'⟩
          exact ⟨j, List.mem_cons_of_mem _ hj, hj'⟩
        · rintro ⟨j, hj, hj'⟩
          rcases List.mem_cons.mp hj with rfl | hj
          · exact absurd h (by simp [hj'])
          · exact ⟨j, hj, hj'⟩
    · simp only [Bool.not_eq_true] at h
      refine ⟨?_, ?_⟩
      · intro s' hs'
        rw [Engine.runTrace_cons, if_neg (by simp [h])] at hs'
        exact absurd hs' (by simp)
      · rw [Engine.runTrace_cons, if_neg (by simp [h])]
        exact ⟨fun _ => ⟨i, List.mem_cons_self, h⟩, fun _ => rfl⟩

end PCA.Coverage

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

