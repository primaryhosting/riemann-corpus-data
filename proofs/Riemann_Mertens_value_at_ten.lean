/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, the partial sums of the
Möbius function.  (The Riemann Hypothesis is equivalent to
`M n = O (n ^ (1/2 + ε))` for every `ε > 0`.) -/
def M (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

/-- `M 10 = -1`: the values `μ 1, …, μ 10` are
`1, -1, -1, 0, -1, 1, -1, 0, 0, 1`, which sum to `-1`. -/
theorem value_at_ten : M 10 = -1 := by
  unfold M
  decide +kernel

end Riemann.Mertens

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

