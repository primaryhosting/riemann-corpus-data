/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- **Mermin/GHZ paradox for local hidden variables.**

A local hidden-variable model for the three-qubit GHZ state assigns to each qubit `i`
predetermined outcomes `a i` (the outcome of measuring `σₓ`) and `b i` (the outcome of
measuring `σ_y`), each of which is `+1` or `-1`, independently of what is measured on the
other qubits.

Quantum mechanics predicts, *deterministically* (the GHZ state is a joint eigenstate of
these four commuting observable products), that `XYY`, `YXY` and `YYX` each yield the
product `+1`, while `XXX` yields the product `-1`.

No local hidden-variable assignment can reproduce all four predictions: multiplying the
first three equations gives `a 0 * a 1 * a 2 * (b 0 * b 1 * b 2)^2 = 1`, and since each
`b i` squares to `1` this forces `a 0 * a 1 * a 2 = 1 ≠ -1`. -/
theorem ghz_nonlocal (a b : Fin 3 → ℤ)
    (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hXYY : a 0 * b 1 * b 2 = 1)
    (hYXY : b 0 * a 1 * b 2 = 1)
    (hYYX : b 0 * b 1 * a 2 = 1) :
    a 0 * a 1 * a 2 ≠ -1 := by
  have hsq : ∀ i, b i * b i = 1 := by
    intro i; rcases hb i with h | h <;> rw [h] <;> norm_num
  have h : (a 0 * b 1 * b 2) * ((b 0 * a 1 * b 2) * (b 0 * b 1 * a 2)) = 1 := by
    rw [hXYY, hYXY, hYYX]; ring
  have expand : (a 0 * b 1 * b 2) * ((b 0 * a 1 * b 2) * (b 0 * b 1 * a 2))
      = (a 0 * a 1 * a 2) * ((b 0 * b 0) * ((b 1 * b 1) * (b 2 * b 2))) := by ring
  rw [expand, hsq 0, hsq 1, hsq 2] at h
  rw [show a 0 * a 1 * a 2 = 1 by simpa using h]
  norm_num

end QC

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

