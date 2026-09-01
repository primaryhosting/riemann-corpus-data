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

namespace Frontier

open Nat.Partrec Nat.Partrec.Code Encodable

/-- **No machine can always correctly predict its own next output.**

Machines are the partial recursive programs of `Nat.Partrec.Code`, and a *predictor* is a
total computable function `predict : ℕ → ℕ` which, given the code of a machine, is supposed
to announce the output that machine produces when run on its own code (its self-application,
i.e. the machine's "next output" about itself).  No such predictor can be correct on every
machine that does produce an output: by Kleene's recursion theorem there is a machine which
reads the prediction made about itself and outputs something different (here, one more).
-/
theorem self_nonprediction :
    ¬ ∃ predict : ℕ → ℕ, Computable predict ∧
        ∀ c : Code, (eval c (encode c)).Dom →
          eval c (encode c) = Part.some (predict (encode c)) := by
  rintro ⟨predict, hpred, hcorrect⟩
  -- The diagonal machine: on any input, output one more than the prediction made about itself.
  have hpartrec : Partrec₂ (fun c : Code => fun _ : ℕ => Part.some (predict (encode c) + 1)) :=
    (Computable.succ.comp (hpred.comp (Computable.encode.comp Computable.fst))).partrec.to₂
  obtain ⟨c, hc⟩ := fixed_point₂ hpartrec
  have hdom : (eval c (encode c)).Dom := by rw [hc]; trivial
  have := hcorrect c hdom
  rw [hc] at this
  simp only [Part.some_inj] at this
  omega

end Frontier

#print axioms Frontier.self_nonprediction

