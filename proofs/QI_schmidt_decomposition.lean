import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
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

namespace QI

variable {A B ι κ : Type*}

/-- `IsON u` says that the family of vectors `u i : A → ℂ` is orthonormal for the standard
hermitian inner product `⟪x, y⟫ = ∑ a, conj (x a) * y a` on `A → ℂ`. -/
def IsON [Fintype A] (u : ι → A → ℂ) : Prop :=
  ∀ i j, ∑ a, star (u i a) * u j a = if i = j then 1 else 0

end QI

