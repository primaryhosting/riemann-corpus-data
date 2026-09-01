/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
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

namespace Math2

open Finset
open scoped FinsetFamily

/-- The **Kruskal-Katona theorem**: given a family `𝒜` of `r`-sets in `Fin n` and an initial
segment `𝒞` of the colex order consisting of `r`-sets with `#𝒞 ≤ #𝒜`, the shadow of `𝒞` is no
bigger than the shadow of `𝒜`.

This is closed by Mathlib's `Finset.kruskal_katona`. -/
theorem kruskal_katona {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (h𝒞𝒜 : #𝒞 ≤ #𝒜)
    (h𝒞 : Finset.Colex.IsInitSeg 𝒞 r) : #(∂ 𝒞) ≤ #(∂ 𝒜) :=
  Finset.kruskal_katona h𝒜r h𝒞𝒜 h𝒞

end Math2

