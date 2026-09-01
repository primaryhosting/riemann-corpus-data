/-
# Psi Shadow
Category: Riemann Program
Target: Riemann.Chebyshev.psi_shadow
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace Chebyshev

/-- **Chebyshev-positivity shadow.** Each summand `Λ(n)^2` occurring in Montgomery's
second moment is nonnegative: for every real `t`, `0 ≤ t ^ 2`.
The proof splits on the sign of `t` and discharges each branch separately. -/
theorem psi_shadow : ∀ t : ℝ, 0 ≤ t ^ 2 := by
  intro t
  rcases le_total 0 t with ht | ht
  · exact pow_nonneg ht 2
  · have h : 0 ≤ (-t) ^ 2 := pow_nonneg (neg_nonneg.mpr ht) 2
    simpa [neg_pow, even_two] using h

end Chebyshev
end Riemann

