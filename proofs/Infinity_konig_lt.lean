import Mathlib

/-!
# Konig Lt
Category: Frontier — Set Theory
Target: Infinity.konig_lt
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Infinity

/-- **König's theorem** (strict sum-vs-product form): if `a i < b i` for every index `i`,
then the cardinal sum of `a` is strictly less than the cardinal product of `b`. -/
theorem konig_lt.{u, v} {ι : Type u} (a b : ι → Cardinal.{v}) (h : ∀ i, a i < b i) :
    Cardinal.sum a < Cardinal.prod b :=
  Cardinal.sum_lt_prod a b h

end Infinity

