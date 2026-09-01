/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph whose vertices carry a linear order:
the sum of the graph distances over all unordered pairs of distinct vertices
(each pair `{u, v}` counted once, via `u < v`). -/
noncomputable def wienerIndex {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2), G.dist p.1 p.2

/-- Along any walk in the path graph, the difference of the endpoint indices is at most
the length of the walk. -/
lemma natAbs_sub_le_walk_length {n : ℕ} {u v : Fin n} (w : (pathGraph n).Walk u v) :
    ((u : ℤ) - (v : ℤ)).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons u x v h p ih =>
    rw [SimpleGraph.pathGraph_adj] at h
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Distance in the path graph is bounded above by the difference of the indices. -/
lemma pathGraph_dist_le_aux {n : ℕ} (d : ℕ) : ∀ (i j : Fin n), (j : ℕ) = (i : ℕ) + d →
    (pathGraph n).dist i j ≤ d := by
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    simp [this]
  | succ d ih =>
    intro i j h
    have hj := j.isLt
    have hk : (i : ℕ) + d < n := by omega
    set k : Fin n := ⟨(i : ℕ) + d, hk⟩ with hkdef
    have h1 : (pathGraph n).dist i k ≤ d := ih i k rfl
    have h2 : (pathGraph n).dist k j = 1 := by
      rw [SimpleGraph.dist_eq_one_iff_adj, SimpleGraph.pathGraph_adj]
      left; simp [hkdef]; omega
    have h3 := (SimpleGraph.pathGraph_preconnected n i k).dist_triangle_left j
    omega

/-- The distance between two vertices of the path graph is the difference of their indices. -/
lemma pathGraph_dist {n : ℕ} (i j : Fin n) (h : (i : ℕ) ≤ (j : ℕ)) :
    (pathGraph n).dist i j = (j : ℕ) - (i : ℕ) := by
  refine le_antisymm (pathGraph_dist_le_aux ((j : ℕ) - (i : ℕ)) i j (by omega)) ?_
  obtain ⟨p, hp⟩ := (SimpleGraph.pathGraph_preconnected n i j).exists_walk_length_eq_dist
  have := natAbs_sub_le_walk_length p
  omega

lemma sum_range_sub_nat (n : ℕ) : ∑ i ∈ Finset.range n, (n - i) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∀ i ∈ Finset.range n, (n + 1 - i) = (n - i) + 1 := by
      intro i hi; simp at hi; omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih]
    simp [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
    omega

lemma sum_pairs_diff (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < j then j - i else 0)
      = (n + 1).choose 3 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    have inner : ∀ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1), (if i < j then j - i else 0))
          = (∑ j ∈ Finset.range n, (if i < j then j - i else 0))
            + (if i < n then n - i else 0) := by
      intro i _; rw [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl inner, Finset.sum_add_distrib, Finset.sum_range_succ
      (fun i => ∑ j ∈ Finset.range n, (if i < j then j - i else 0)),
      Finset.sum_range_succ (fun i => if i < n then n - i else 0), ih]
    have h1 : (∑ j ∈ Finset.range n, (if n < j then j - n else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj; simp at hj; simp; omega
    have h2 : (∑ i ∈ Finset.range n, (if i < n then n - i else 0))
        = ∑ i ∈ Finset.range n, (n - i) := by
      apply Finset.sum_congr rfl; intro i hi; simp at hi; simp [hi]
    rw [h1, h2, sum_range_sub_nat]
    simp [Nat.choose_succ_succ (n + 1) 2]
    omega

/-- **Wiener index of the path graph**: the Wiener index of `P_n` equals `C(n+1, 3)`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  rw [wienerIndex, Finset.sum_filter, Fintype.sum_prod_type]
  have key : ∀ i : Fin n, (∑ j : Fin n, if i < j then (pathGraph n).dist i j else 0)
      = ∑ j ∈ Finset.range n, (if (i : ℕ) < j then j - (i : ℕ) else 0) := by
    intro i
    rw [← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < j then j - (i : ℕ) else 0) n]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hij : (i : ℕ) < (j : ℕ)
    · rw [if_pos (Fin.lt_def.2 hij), if_pos hij, pathGraph_dist i j (le_of_lt hij)]
    · rw [if_neg (fun h => hij (Fin.lt_def.1 h)), if_neg hij]
  rw [Finset.sum_congr rfl (fun i _ => key i),
    Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, (if i < j then j - i else 0)) n]
  exact sum_pairs_diff n

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

