import Mathlib

/-!
# Fib Uniform Mod 5
Category: Cone Line
Target: Brockian.ConeLine.fib_uniform_mod5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to come before any module docstring,
-- so the required header block is placed immediately after the single import.

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Brockian
namespace ConeLine

/-- Within one Pisano period (the first 20 Fibonacci numbers), each residue
class mod 5 occurs exactly 4 times: Fibonacci is uniformly distributed mod 5. -/
theorem fib_uniform_mod5 (r : Fin 5) :
    ((Finset.range 20).filter (fun k => Nat.fib k % 5 = r.val)).card = 4 := by
  fin_cases r <;> decide

/-- The Pisano period 20 restart seed: `fib 20 ≡ 0` and `fib 21 ≡ 1` mod 5. -/
theorem fib_pisano20_seed : Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1 := by
  constructor <;> decide

end ConeLine
end Brockian

