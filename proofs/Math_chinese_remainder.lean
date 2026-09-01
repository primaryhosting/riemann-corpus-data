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

namespace Math

open scoped Function in
/-- **Chinese remainder theorem**: for a finite family of pairwise coprime moduli `a i`,
the ring `ZMod (∏ i, a i)` is isomorphic to the product ring `Π i, ZMod (a i)`,
and the isomorphism is given by the natural reduction maps. -/
theorem chinese_remainder {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    ∃ e : ZMod (∏ i, a i) ≃+* (Π i, ZMod (a i)),
      ∀ (x : ZMod (∏ i, a i)) (i : ι),
        e x i = ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)) x := by
  refine ⟨ZMod.prodEquivPi a coprime, fun x i => ?_⟩
  have h : (Pi.evalRingHom (fun i => ZMod (a i)) i).comp
      (ZMod.prodEquivPi a coprime : ZMod (∏ i, a i) →+* (Π i, ZMod (a i)))
      = ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)) :=
    RingHom.ext_zmod _ _
  exact congrArg (fun f => f x) h

end Math

