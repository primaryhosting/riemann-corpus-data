import Mathlib

/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

/-- **Handshake valence.**  Model a molecule as a finite simple graph `G`: the vertices are
atoms and the edges are bonds.  The *valence* of an atom is its degree, i.e. the number of
bonds incident to it.  Then the sum of the valences of all atoms equals twice the number of
bonds.

This is the handshaking lemma, available in Mathlib as
`SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem handshake_valence {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∑ a : V, G.degree a = 2 * #G.edgeFinset :=
  G.sum_degrees_eq_twice_card_edges

end Chem

