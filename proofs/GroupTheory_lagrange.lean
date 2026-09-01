import Mathlib

/-!
# Lagrange
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.lagrange
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace GroupTheory

/-- **Lagrange's theorem**: for a finite group `G` and a subgroup `H`, the cardinality of `H`
divides the cardinality of `G`. -/
theorem lagrange {G : Type*} [Fintype G] [Group G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G :=
  by simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H

end GroupTheory

