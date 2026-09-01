/-
# Fib Uniform Mod 5
Category: Cone Line
Target: Brockian.ConeLine.fib_uniform_mod5
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

set_option grind.warning false

namespace Brockian.ConeLine

/-- Within one Pisano period (20 terms), each residue mod 5 occurs exactly 4 times
among `Nat.fib k % 5` for `k < 20`; together with the Pisano-20 restart
`fib 20 % 5 = 0` and `fib 21 % 5 = 1`. -/
theorem fib_uniform_mod5 :
    (∀ r : Fin 5,
      ((Finset.range 20).filter (fun k => Nat.fib k % 5 = r.val)).card = 4) ∧
    Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  decide

end Brockian.ConeLine

