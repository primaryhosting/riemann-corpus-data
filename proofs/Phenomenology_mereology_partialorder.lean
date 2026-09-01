import Mathlib

/-!
# Mereology Partialorder
Category: Frontier — Set Theory
Target: Phenomenology.mereology_partialorder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Phenomenology

/--
A faithful formal fragment of Husserlian part-whole structure (mereology), stated as a MODEL
of a phenomenological structure, not as a claim about consciousness.

`part-of` is modelled by the partial order `≤` on a type `P` (reflexive, antisymmetric,
transitive), and `proper-part-of` by the strict order `<`. The theorem records that:

* the whole (the `⊤` element, when present) has every element as a part;
* proper-part-of is irreflexive;
* proper-part-of is transitive.
-/
theorem mereology_partialorder (P : Type*) [PartialOrder P] [OrderTop P] :
    (∀ x : P, x ≤ (⊤ : P)) ∧ (∀ x : P, ¬ (x < x)) ∧
      (∀ x y z : P, x < y → y < z → x < z) :=
  ⟨fun _ => le_top, fun x => lt_irrefl x, fun _ _ _ hxy hyz => lt_trans hxy hyz⟩

end Phenomenology

