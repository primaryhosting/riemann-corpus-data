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

import Mathlib
/-!
# Nat Countable
Category: Frontier — Set Theory
Target: Infinity.nat_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- `Nat` is countable: there is an injection from `Nat` into `Nat`. -/
theorem countable_nat : Countable Nat :=
  ⟨⟨id, fun _ _ h => h⟩⟩

/-- `Nat` is infinite: it admits an injection from itself that is not surjective;
equivalently, it is not a finite type. -/
theorem infinite_nat : Infinite Nat :=
  Infinite.of_not_fintype fun _ => by
    have h : Finset.univ.sup id + 1 ≤ Finset.univ.sup id :=
      Finset.le_sup (f := id) (Finset.mem_univ (Finset.univ.sup id + 1))
    omega

/-- The naturals are countably infinite: `Nat` is a `Countable` type and is `Infinite`. -/
theorem nat_countable : Countable Nat ∧ Infinite Nat :=
  ⟨countable_nat, infinite_nat⟩

end Infinity

