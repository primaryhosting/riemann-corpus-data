import Mathlib

/-!
# Measurable Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.measurable_statement
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


universe u

namespace LargeCardinal

/-- `IsMeasurable kappa` says that the cardinal `kappa` is a measurable cardinal:
`kappa` is uncountable and there is a nonprincipal, `kappa`-complete ultrafilter on
a type of cardinality `kappa` (namely `kappa.ord.ToType`).

Here `kappa`-completeness means: for every family `s` of fewer than `kappa` many sets,
all belonging to the ultrafilter, the intersection `⋂₀ s` again belongs to it. -/
def IsMeasurable (kappa : Cardinal.{u}) : Prop :=
  Cardinal.aleph0 < kappa ∧
    ∃ U : Ultrafilter kappa.ord.ToType,
      (∀ x : kappa.ord.ToType, ({x} : Set kappa.ord.ToType) ∉ U) ∧
      (∀ s : Set (Set kappa.ord.ToType),
        Cardinal.mk s < kappa → (∀ t ∈ s, t ∈ U) → ⋂₀ s ∈ U)

/-- The measurable-cardinal statement: there exists a measurable cardinal.
This is a large-cardinal axiom; it is *not* provable in ZFC (it implies `Con(ZFC)`),
so we only register the statement here. -/
def MeasurableCardinalExists : Prop := ∃ kappa : Cardinal.{u}, IsMeasurable kappa

/-- The target: the self-equivalence of the measurable-cardinal statement.
No existence claim is made. -/
theorem measurable_statement :
    MeasurableCardinalExists.{u} ↔ MeasurableCardinalExists.{u} := Iff.rfl

end LargeCardinal

