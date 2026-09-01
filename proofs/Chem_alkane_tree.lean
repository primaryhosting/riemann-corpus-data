import Mathlib

/-!
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option autoImplicit false

namespace Chem

/-- **The carbon skeleton of an acyclic alkane is a tree with `n - 1` C–C bonds.**

The carbon skeleton is modelled as a finite simple graph `G` on the set of carbon atoms:
`G.Adj u v` means there is a C–C bond between `u` and `v`.  The chemical hypotheses are

* `hconn`  : the molecule is a single connected species;
* `hacyc`  : the molecule is acyclic (no rings);
* `hdeg`   : carbon is tetravalent, so each carbon has at most four C–C bonds;

Writing `n = Fintype.card V` for the number of carbons, we conclude:

1. the skeleton is a tree;
2. it has exactly `n - 1` C–C bonds (stated as `edges + 1 = n` to avoid truncated subtraction);
3. the number of hydrogens, each carbon carrying `4 - (number of C–C bonds at it)` of them,
   is `2n + 2`, i.e. the molecular formula is `CₙH₂ₙ₊₂`.
-/
theorem alkane_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hacyc : G.IsAcyclic)
    (hdeg : ∀ v : V, G.degree v ≤ 4) :
    G.IsTree ∧ G.edgeFinset.card + 1 = Fintype.card V ∧
      ∑ v : V, (4 - G.degree v) = 2 * Fintype.card V + 2 := by
  have htree : G.IsTree := ⟨hconn, hacyc⟩
  have hcard : G.edgeFinset.card + 1 = Fintype.card V := htree.card_edgeFinset
  refine ⟨htree, hcard, ?_⟩
  have hsum : (∑ v : V, (4 - G.degree v)) + ∑ v : V, G.degree v = 4 * Fintype.card V := by
    rw [← Finset.sum_add_distrib]
    have : ∀ v ∈ (Finset.univ : Finset V), (4 - G.degree v) + G.degree v = 4 := fun v _ =>
      Nat.sub_add_cancel (hdeg v)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.mul_comm]
  have hhand : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  omega

end Chem

