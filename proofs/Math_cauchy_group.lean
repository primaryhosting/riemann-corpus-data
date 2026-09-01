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

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`,
then `G` contains an element of order `p`. -/
theorem cauchy_group {G : Type*} [Group G] [Fintype G] {p : ℕ} (hp : Nat.Prime p)
    (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card p hdvd

end Math

