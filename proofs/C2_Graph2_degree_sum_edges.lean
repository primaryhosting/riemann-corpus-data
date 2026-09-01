import Mathlib
open Finset
namespace C2.Graph2

/-- The sum of the degrees of a finite simple graph is `2 * |E|`. -/
theorem degree_sum_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

/-- The handshake lemma: the sum of the degrees of a finite simple graph is even. -/
theorem sum_degrees_even {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (∑ v, G.degree v) := by
  rw [degree_sum_edges]
  exact even_two_mul _

/-- A finite tree on `n` vertices has `n - 1` edges. -/
theorem tree_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.IsTree) : G.edgeFinset.card + 1 = Fintype.card V :=
  ht.card_edgeFinset

end C2.Graph2

