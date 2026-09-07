import Mathlib

/-!
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Ordinal

/-- Every normal function on the ordinals has a fixed point above any given ordinal,
obtained as the normal fixed point (`Ordinal.nfp`) of the function at that ordinal. -/
theorem exists_fixed_point_of_isNormal {f : Ordinal → Ordinal} (hf : Order.IsNormal f)
    (a : Ordinal) : ∃ o : Ordinal, a ≤ o ∧ f o = o :=
  ⟨nfp f a, le_nfp f a, nfp_fp hf a⟩

end Ordinal

namespace Cardinal

/-- **Aleph fixed point.** The aleph function, viewed as a normal function on the
ordinals via `Cardinal.ord`, has a fixed point: there is an ordinal `o` with
`(aleph o).ord = o`. -/
theorem aleph_fixed_point_statement : ∃ o : Ordinal, (Cardinal.aleph o).ord = o := by
  obtain ⟨o, -, ho⟩ := Ordinal.exists_fixed_point_of_isNormal Ordinal.isNormal_omega 0
  exact ⟨o, by rw [Cardinal.ord_aleph]; exact ho⟩

/-- There are arbitrarily large aleph fixed points. -/
theorem exists_ge_aleph_fixed_point (a : Ordinal) :
    ∃ o : Ordinal, a ≤ o ∧ (Cardinal.aleph o).ord = o := by
  obtain ⟨o, hao, ho⟩ := Ordinal.exists_fixed_point_of_isNormal Ordinal.isNormal_omega a
  exact ⟨o, hao, by rw [Cardinal.ord_aleph]; exact ho⟩

end Cardinal

