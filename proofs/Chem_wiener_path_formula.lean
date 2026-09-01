import Mathlib

open scoped BigOperators
open scoped Nat

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs (the diagonal contributes `0`). -/
noncomputable def wienerIndex {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (∑ u : V, ∑ v : V, G.dist u v) / 2

/-- Any walk in the path graph is at least as long as the numerical distance
between its endpoints. -/
lemma natDist_le_walk_length {n : ℕ} :
    ∀ {i j : Fin n} (w : (pathGraph n).Walk i j), Nat.dist (i : ℕ) (j : ℕ) ≤ w.length := by
  intro i j w
  induction w with
  | nil => simp
  | cons h w ih =>
      rename_i i k j
      have h1 : Nat.dist (i : ℕ) (k : ℕ) = 1 := by
        rcases (pathGraph_adj).1 h with h' | h' <;> simp [Nat.dist] <;> omega
      calc Nat.dist (i : ℕ) (j : ℕ) ≤ Nat.dist (i : ℕ) (k : ℕ) + Nat.dist (k : ℕ) (j : ℕ) :=
            Nat.dist.triangle_inequality _ _ _
        _ ≤ 1 + w.length := by rw [h1]; exact Nat.add_le_add_left ih 1
        _ = (SimpleGraph.Walk.cons h w).length := by simp [Nat.add_comm]

/-- Existence of a geodesic walk in the path graph, in the ordered case. -/
lemma exists_walk_le {n : ℕ} :
    ∀ (d : ℕ) (i j : Fin n), (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) = d →
      ∃ w : (pathGraph n).Walk i j, w.length = d := by
  intro d
  induction d with
  | zero =>
      intro i j hij h
      have : i = j := Fin.ext (by omega)
      subst this
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
      intro i j hij h
      have hjn : (j : ℕ) < n := j.isLt
      have hk : (i : ℕ) + 1 < n := by omega
      let k : Fin n := ⟨(i : ℕ) + 1, hk⟩
      have hadj : (pathGraph n).Adj i k := pathGraph_adj.2 (Or.inl rfl)
      obtain ⟨w, hw⟩ := ih k j (by simp [k]; omega) (by simp [k]; omega)
      exact ⟨SimpleGraph.Walk.cons hadj w, by simp [hw]⟩

/-- Existence of a geodesic walk in the path graph. -/
lemma exists_walk_natDist {n : ℕ} (i j : Fin n) :
    ∃ w : (pathGraph n).Walk i j, w.length = Nat.dist (i : ℕ) (j : ℕ) := by
  rcases le_total (i : ℕ) (j : ℕ) with h | h
  · obtain ⟨w, hw⟩ := exists_walk_le (Nat.dist (i : ℕ) (j : ℕ)) i j h (by simp [Nat.dist]; omega)
    exact ⟨w, hw⟩
  · obtain ⟨w, hw⟩ := exists_walk_le (Nat.dist (j : ℕ) (i : ℕ)) j i h (by simp [Nat.dist]; omega)
    exact ⟨w.reverse, by simpa [Nat.dist_comm] using hw⟩

/-- The distance between two vertices of the path graph `P_n` is the absolute
difference of their indices. -/
theorem pathGraph_dist {n : ℕ} (i j : Fin n) :
    (pathGraph n).dist i j = Nat.dist (i : ℕ) (j : ℕ) := by
  obtain ⟨w, hw⟩ := exists_walk_natDist i j
  refine le_antisymm (hw ▸ SimpleGraph.dist_le w) ?_
  obtain ⟨p, hp⟩ := (SimpleGraph.Walk.reachable w).exists_walk_length_eq_dist
  calc Nat.dist (i : ℕ) (j : ℕ) ≤ p.length := natDist_le_walk_length p
    _ = (pathGraph n).dist i j := hp

lemma sum_range_succ_eq_choose (n : ℕ) : ∑ i ∈ range n, (i + 1) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (n + 1) 1]
      simp [Nat.add_comm]

lemma sum_natDist_last (n : ℕ) : ∑ i ∈ range n, Nat.dist i n = (n + 1).choose 2 := by
  rw [← sum_range_succ_eq_choose n, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Nat.dist]
  omega

lemma sum_natDist_range (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, Nat.dist i j = 2 * (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), Nat.dist i j
          = (∑ j ∈ range n, Nat.dist i j) + Nat.dist i n := fun i _ => Finset.sum_range_succ _ _
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, sum_natDist_last,
        Finset.sum_range_succ]
      have h2 : ∑ j ∈ range n, Nat.dist n j = (n + 1).choose 2 := by
        rw [← sum_natDist_last n]
        exact Finset.sum_congr rfl fun i _ => Nat.dist_comm n i
      rw [h2, Nat.dist_self]
      have h3 : (n + 2).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 :=
        Nat.choose_succ_succ (n + 1) 2
      have h4 : (n + 1 + 1).choose 3 = (n + 2).choose 3 := rfl
      omega

/-- **The Wiener index of the path graph `P_n` is `C(n+1, 3)`.** -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  have h : ∑ i : Fin n, ∑ j : Fin n, (pathGraph n).dist i j = 2 * (n + 1).choose 3 := by
    have inner : ∀ i : Fin n, ∑ j : Fin n, Nat.dist (i : ℕ) (j : ℕ)
        = ∑ j ∈ range n, Nat.dist (i : ℕ) j :=
      fun i => Fin.sum_univ_eq_sum_range (fun j => Nat.dist (i : ℕ) j) n
    rw [← sum_natDist_range n]
    simp only [pathGraph_dist, inner]
    exact Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, Nat.dist i j) n
  rw [wienerIndex, h, Nat.mul_div_cancel_left _ (by norm_num)]

end Chem

