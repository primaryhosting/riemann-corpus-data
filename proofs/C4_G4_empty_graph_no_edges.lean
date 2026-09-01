import Mathlib
open Finset
namespace C4.G4

/-- The empty graph has no edges. -/
theorem empty_graph_no_edges {V : Type*} [Fintype V] [DecidableEq V] :
    (⊥ : SimpleGraph V).edgeFinset.card = 0 := by
  simp

/-- The edges of a graph and of its complement partition the edges of the complete
graph, so their numbers add up to `(card V).choose 2`. -/
theorem self_complementary_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have h : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, SimpleGraph.top_adj]
      exact ⟨fun h => h.elim (fun h => G.ne_of_adj h) (fun h => h.1),
        fun h => (em (G.Adj x y)).imp id (fun h' => ⟨h, h'⟩)⟩
  rw [← Finset.card_union_of_disjoint hd, h,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-- Placeholder statement as given in the original file. -/
theorem path_graph_degree : True := trivial

end C4.G4

