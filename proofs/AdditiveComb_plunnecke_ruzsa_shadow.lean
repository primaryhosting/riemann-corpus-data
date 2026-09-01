import Mathlib

/-!
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
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


namespace AdditiveComb

/-- **Ruzsa's triangle inequality** (the engine of Plünnecke–Ruzsa), for finite nonempty
sets `A`, `B`, `C` of integers:
`|A - C| * |B| ≤ |A - B| * |B - C|`. -/
theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hC : C.Nonempty) :
    (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  have hCB : (C - B).card = (B - C).card := by
    rw [← Finset.card_neg (B - C)]
    congr 1
    ext x
    simp [Finset.mem_sub]
  rwa [hCB] at h

end AdditiveComb

