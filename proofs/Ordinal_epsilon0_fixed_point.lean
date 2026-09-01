import Mathlib
-- Note: Lean 4 requires `import` lines to come first in a file, so the required
-- header comment appears immediately below the import.
/-!
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
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

set_option grind.warning false

namespace Ordinal

open scoped Ordinal

/-- `ε₀` is a fixed point of ordinal `ω`-exponentiation: `ω ^ ε₀ = ε₀`. -/
theorem epsilon0_fixed_point : Ordinal.omega0 ^ Ordinal.epsilon 0 = Ordinal.epsilon 0 :=
  omega0_opow_epsilon 0

/-- `ε₀` is the *least* ordinal fixed by `ω`-exponentiation. -/
theorem epsilon0_least_fixed_point (o : Ordinal)
    (ho : Ordinal.omega0 ^ o = o) : Ordinal.epsilon 0 ≤ o :=
  epsilon_zero_le_of_omega0_opow_le ho.le

end Ordinal

#print axioms Ordinal.epsilon0_fixed_point
#print axioms Ordinal.epsilon0_least_fixed_point

