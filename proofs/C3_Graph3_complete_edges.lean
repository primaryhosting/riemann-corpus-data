import Mathlib
open Finset
namespace C3.Graph3
theorem complete_edges (n : ℕ) : (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2 := by
  simpa using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
theorem handshake2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges
theorem odd_degree_even_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (univ.filter (fun v => Odd (G.degree v))).card := by
  simpa [Set.toFinset_setOf] using G.even_card_odd_degree_vertices
end C3.Graph3

