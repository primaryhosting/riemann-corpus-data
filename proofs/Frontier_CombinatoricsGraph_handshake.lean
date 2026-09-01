import Mathlib
open Finset
namespace Frontier.CombinatoricsGraph
theorem handshake {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (∑ v, G.degree v) := by
  rw [G.sum_degrees_eq_twice_card_edges]
  exact even_two_mul _
theorem sum_odds (n : ℕ) : ∑ i ∈ range n, (2*i+1) = n^2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring
theorem hockey_stick (n k : ℕ) : ∑ i ∈ range (n+1), i.choose k = (n+1).choose (k+1) := by
  induction n with
  | zero => simp [Nat.choose_succ_succ]
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (n+1) k, Nat.add_comm]
end Frontier.CombinatoricsGraph

