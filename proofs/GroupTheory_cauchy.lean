import Mathlib

/-!
# Cauchy
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.cauchy
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

/-- **Cauchy's theorem**: if a prime `p` divides the cardinality of a finite group `G`,
then `G` contains an element of order `p`.

This is Mathlib's `exists_prime_orderOf_dvd_card`
(`Mathlib/GroupTheory/Perm/Cycle/Type.lean`), restated with the primality of `p`
as an explicit hypothesis rather than a `Fact` instance. -/
theorem GroupTheory.cauchy {G : Type*} [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  haveI : Fact p.Prime := ⟨hp⟩
  exists_prime_orderOf_dvd_card p hdvd

