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
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal

namespace Cardinal

/-- Every normal function on the ordinals has a fixed point: the normal fixed point
construction `Ordinal.nfp` applied to any starting ordinal yields one
(`Ordinal.nfp_fp`). -/
theorem exists_fixed_point_of_isNormal {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Order.IsNormal f) : ∃ a : Ordinal.{u}, f a = a :=
  ⟨Ordinal.nfp f 0, Ordinal.nfp_fp hf 0⟩

/-- **Aleph fixed point.** The map `o ↦ (ℵ_ o).ord = ω_ o` is a normal function on the
ordinals, hence it has a fixed point: there is an ordinal `o` with `(aleph o).ord = o`,
i.e. an ordinal which is its own `o`-th infinite initial ordinal. -/
theorem aleph_fixed_point_statement : ∃ o : Ordinal.{u}, (Cardinal.aleph o).ord = o := by
  obtain ⟨o, ho⟩ := exists_fixed_point_of_isNormal Ordinal.isNormal_omega
  exact ⟨o, by rwa [Cardinal.ord_aleph]⟩

end Cardinal

