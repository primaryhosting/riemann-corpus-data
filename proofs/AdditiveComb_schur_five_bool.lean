/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

/-- Boolean core of the Schur bound `S(2) < 5`: for any five booleans
`a, b, c, d, e` (the colours of `1, 2, 3, 4, 5`) at least one of the five listed
monochromatic patterns occurs.  They correspond to the Schur triples
`1 + 1 = 2`, `1 + 3 = 4`, `2 + 2 = 4`, `1 + 4 = 5` and `2 + 3 = 5`. -/
theorem schur_five_bool (a b c d e : Bool) :
    a = b ∨ (a = c ∧ c = d) ∨ b = d ∨ (a = d ∧ d = e) ∨ (b = c ∧ c = e) := by
  revert a b c d e
  decide

/-- **Schur instance `S(2) < 5`.**

Every 2-colouring of `{1, 2, 3, 4, 5}` contains a monochromatic Schur triple, i.e.
elements `p, q, r` of the same colour with `p + q = r`.

The colouring is given by a function `f : Fin 5 → Bool`, where the index `x : Fin 5`
represents the integer `x.val + 1 ∈ {1, …, 5}`. The conclusion produces indices
`x, y, z` whose represented values satisfy `(x.val + 1) + (y.val + 1) = z.val + 1`
and which all receive the same colour. (As usual for Schur triples, `x` and `y`
are allowed to be equal.) -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5, x.val + 1 + (y.val + 1) = z.val + 1 ∧
      f x = f y ∧ f y = f z := by
  rcases schur_five_bool (f 0) (f 1) (f 2) (f 3) (f 4) with
    h | ⟨h₁, h₂⟩ | h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨0, 0, 1, rfl, rfl, h⟩
  · exact ⟨0, 2, 3, rfl, h₁, h₂⟩
  · exact ⟨1, 1, 3, rfl, rfl, h⟩
  · exact ⟨0, 3, 4, rfl, h₁, h₂⟩
  · exact ⟨1, 2, 4, rfl, h₁, h₂⟩

end AdditiveComb

import Mathlib
import RequestProject.SchurFive

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

